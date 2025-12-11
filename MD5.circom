pragma circom 2.1.4;

// n is the number of bits
template LocalNum2Bits(n){
    signal input in;
    signal output out[n];

    var lc1=0;

    var p = 1;
    for (var i = 0; i < n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        // Reconstructs the number to compare at the end
        lc1 += out[i] * p;
        p = p * 2;
    }

    lc1 === in;
}

// n is the number of bits received to simulate to num
template LocalBits2Num(n){
    signal input in[n];
    signal output out;

    var lc = 0;
    var p = 1;  
    
    for (var i = 0; i < n; i++){

        // Constrain inputs to be 0 or 1
        in[i] * (in[i] - 1) === 0;
        
        lc += in[i] * p;
        p = p * 2;  
    }
    
    lc ==> out;
}


template LocalisZero(){
    signal input in[2];

    // make sure the inputs 0 or 1
    in[0] * (in[0] - 1) === 0;
    in[1] * (in[1] - 1) === 0;
}

template LocalAND(){
    signal input in[2];
    signal output out;

    component isZero = LocalisZero();
    isZero.in[0] <== in[0];
    isZero.in[1] <== in[1];

    out <== in[0] * in[1];

}

template LocalOR(){
    signal input in[2];
    signal output out;

    component isZero = LocalisZero();
    isZero.in[0] <== in[0];
    isZero.in[1] <== in[1];

    // checking if any if the input values is 1
    signal add;
    in[0] + in [1] ==> add;

    signal res;
    res <-- add != 0 ? 1 : 0;

    res ==> out;

}

template LocalNOT(){
    signal input in;
    signal output out;

    // make sure the input 0 or 1
    in * (in - 1) === 0;

    out <== 1 - in;
}

template LocalXOR(){
    signal input in[2];
    signal output out;

    component isZero = LocalisZero();
    isZero.in[0] <== in[0];
    isZero.in[1] <== in[1];

    // you might wounder what if in[0] = 0 and in[1] = 1 shouldn't that result in -1 
    signal diff;
    in[0] - in[1] ==> diff;

    signal res;
    res <-- diff != 0 ? 1 : 0;

    res ==> out;
}

// n is the number of bits to rotate 
template LocalLeftRotate(n){
    signal input in;
    signal output out;

    component n2b = LocalNum2Bits(32);
    component b2n = LocalBits2Num(32);

    n2b.in <== in;

    var x = 0;
    for (var i = 0; i < 32; i++) {
        x = (i + n) % 32;
        b2n.in[x] <== n2b.out[i];
    }

    out <== b2n.out;
}

// the overflow for the 32 bit addition
template LocalOverFlow(){
    signal input in;
    signal output out;

    component n2b = LocalNum2Bits(252);
    component b2n = LocalBits2Num(32);

    n2b.in <== in;
    // only take the least significant 32 bit
    for (var i = 0; i < 32; i++) {
        n2b.out[i] ==> b2n.in[i];
    }

    b2n.out ==> out;
}

// the combine function
// f(b,c,d,i)
template LocalCombine (i){
    // these are the required operations for the combining
    /*
        if i <= 16:
        out = (B & C) | (~B & D)

    elif i > 16 and i <= 32:
        out = (D & B) | (~D & C)

    elif i > 32 and i <= 48:
        out = B ^ C ^ D

    elif i > 48 and i <= 64:
        out = C ^ (B | ~D)

    else:
        assert False, "1) What"

    return out
    */

    // because the max no. of iteration is 64
    assert(i <= 64);
    input signal b;
    input signal c;
    input signal d;
    signal output out;

    if (i <= 16){
        // (B & C) 
        component op1_1 = LocalAND(); 
        op1_1.in[0] <== b;
        op1_1.in[1] <== c;

        // ~B
        component NotB = LocalNOT();
        NotB.in <== b;

        // (~B & D)
        component op2_1 = LocalAND();
        op2_1.in[0] <== NotB.out;
        op2_1.in[1] <== d;

        // (B & C) | (~B & D)
        component op3 = LocalOR();
        op3.in[0] <== op1_1.out;
        op3.in[1] <== op2_1.out;

        op3.out ==> out;

    }else if(i > 16 && i <= 32){
        // (D & B)
        component op1_2 = LocalAND();
        op1_2.in[0] <== d;
        op1_2.in[1] <== b;

        // ~D
        component NotD = LocalNOT();
        NotD.in <== d;

        // (~D & C)
        component op2_0 = LocalAND();
        op2_0.in[0] <== NotD.out;
        op2_0.in[1] <== c;

        // (D & B) | (~D & C)
        component op3 = LocalOR();
        op3.in[0] <== op1_2.out;
        op3.in[1] <== op2_0.out;

        op3.out ==> out;

    }else if (i > 32 && i <= 48){
        // B ^ C
        component op1_3 = LocalXOR();
        op1_3.in[0] <== b;
        op1_3.in[1] <== c;

        // B ^ C ^ D
        component op2_2 = LocalXOR();
        op2_2.in[0] <== op1_3.out;
        op2_2.in[1] <== d;

        op2_2.out ==> out;

    }else{
        // ~D
        component NotD = LocalNOT();
        NotD.in <== d;

        // (B | ~D)
        component op1_4 = LocalOR();
        op1_4.in[0] <== b;
        op1_4.in[1] <== NotD.out;

        // C ^ (B | ~D)
        component op2_2 = LocalXOR();
        op2_2.in[0] <== c;
        op2_2.in[1] <== op1_4.out;

        op2_2.out ==> out;
    }
}

// n is the number of bytes
template Padding(n) {
    assert(n < 56);

    signal input in[n];

    // 64 bytes
    signal output out[64];

    for (var i = 0; i < n; i++) {
        out[i] <== in[i];
    }

    // the rest of the template was inspired by rareskills article

    // add 128 = 0x80 to pad the 1 bit (0x80 = 10000000b)
    out[n] <== 128;

    // pad the rest with zeros
    for (var i = n + 1; i < 56; i++) {
        out[i] <== 0;
    }

    var lenBits = n * 8;
    if (lenBits < 256) {
        out[56] <== lenBits;
    }
    else {
        var lowOrderBytes = lenBits % 256;
        var highOrderBytes = lenBits \ 256;
        out[56] <== lowOrderBytes;
        out[57] <== highOrderBytes;
    }
}

// n is number of bytes
template ToBytes(n) {
    signal input in;
    signal output out[n];

    component n2b = LocalNum2Bits(n * 8);
    n2b.in <== in;

    component b2n2[n];
    for (var i = 0; i < n; i++) {
        b2n2[i] = LocalBits2Num(8);
        for (var j = 0; j < 8; j++) {
            var x = 8 * i + j;
            b2n2[i].in[j] <== n2b.out[x];
        }
        out[i] <== b2n2[i].out;
    }
}

template MD5(n){
    signal input in[n];

    var s[64] = [7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22,
     5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20,
     4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23,
    6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21];

    var K[64] = [0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
     0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
     0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
     0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
     0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
     0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
     0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
     0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
     0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
     0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
     0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
     0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
     0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
     0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
     0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
     0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391];

    var iter_to_index[64] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
     1, 6, 11, 0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12,
     5, 8, 11, 14, 1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 15, 2,
    0, 7, 14, 5, 12, 3, 10, 1, 8, 15, 6, 13, 4, 11, 2, 9];

    // this part is inspired by rareskills article

    signal word64[64];
    component pad = Padding(n);

    for (var i = 0; i < n; i++) {
        pad.in[i] <== in[i];
    }
    for (var i = 0; i < 64; i++) {
        pad.out[i] ==> word64[i];
    }

    signal bit32[16];
    for (var i = 0; i < 16; i++) {
        bit32[i] <== word64[4 * i] + word64[4 * i + 1] * 2**8 + word64[4 * i + 2] * 2**16 + word64[4 * i + 3] * 2**24;
    }

    var A = 0;
    var B = 1;
    var C = 2;
    var D = 3;
    signal screw[65][4];
    // the hardcoded initial state
    screw[0][A] <== 1732584193;
    screw[0][B] <== 4023233417;
    screw[0][C] <== 2562383102;
    screw[0][D] <== 271733878;

    component combine[64];
    component SelectInputWords[64];
    signal toRotates[64];
    component rotateLeft[64];
    component flow32[64];
    component flow32s2[64];
    for (var i = 0; i < 64; i++) {
        combine[i] = LocalCombine(i);
        combine[i].b <== screw[i][B];
        combine[i].c <== screw[i][C];
        combine[i].d <== screw[i][D];

        flow32[i] = LocalOverFlow();
        flow32[i].in <== screw[i][A] + combine[i].out + K[i] + bit32[iter_to_index[i]];

        toRotates[i] <== flow32[i].out;
        rotateLeft[i] = LocalLeftRotate(s[i]);
        rotateLeft[i].in <== toRotates[i];

        flow32s2[i] = LocalOverFlow();
        flow32s2[i].in <== rotateLeft[i].out + screw[i][B];

        screw[i + 1][A] <== screw[i][D];
        screw[i + 1][B] <== flow32s2[i].out;
        screw[i + 1][C] <== screw[i][B];
        screw[i + 1][D] <== screw[i][C];
    }

    component addA = LocalOverFlow();
    component addB = LocalOverFlow();
    component addC = LocalOverFlow();
    component addD = LocalOverFlow();

    addA.in <== 1732584193 + screw[64][A];
    addB.in <== 4023233417 + screw[64][B];
    addC.in <== 2562383102 + screw[64][C];
    addD.in <== 271733878 + screw[64][D];

    signal littleEndian;
    littleEndian <== addA.out + addB.out * 2**32 + addC.out * 2**64 + addD.out * 2**96;

    component Tb = ToBytes(16);
    Tb.in <== littleEndian;

    var acc;
    for (var i = 0; i < 16; i++) {
        acc += Tb.out[15 - i] * 2**(i * 8);
    }
    signal output out;
    out <== acc;
}

component main = MD5(10);