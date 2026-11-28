# The Speck round function

Speck is an ARX block cipher family: on two $k$-bit words, a round maps $(x,y)$ to $\bigl((x\ggg\alpha)\boxplus y)\oplus K,\ (y\lll\beta)\oplus((x\ggg\alpha)\boxplus y)\oplus K\bigr)$, with $(\alpha,\beta)=(7,2)$ for Speck32/64, which has 22 rounds.

Fix a word size $k$ and rotation amounts $\alpha,\beta$. For a round key $K\in\{0,1\}^k$ the Speck round function on a state of two $k$-bit words $(x,y)$ is

$$
R_K(x,y)=\bigl(((x\ggg\alpha)\boxplus y)\oplus K,\ \ (y\lll\beta)\oplus((x\ggg\alpha)\boxplus y)\oplus K\bigr),
$$

where $\boxplus$ is addition modulo $2^k$, $\oplus$ is bitwise exclusive or, and $\ggg,\lll$ are rotations right and left. Equivalently, with $(L_i,R_i)$ the state, $L_{i+1}=((L_i\ggg\alpha)\boxplus R_i)\oplus K_i$ and $R_{i+1}=(R_i\lll\beta)\oplus L_{i+1}$. The amounts are $\alpha=7$, $\beta=2$ when the block size is $32$ ($k=16$), and $\alpha=8$, $\beta=3$ otherwise. The inverse uses modular subtraction: $R_K^{-1}(x,y)=\bigl(((x\oplus K)\boxminus((x\oplus y)\ggg\beta))\lll\alpha,\ (x\oplus y)\ggg\beta\bigr)$.

**Speck32/64** has a 32-bit block, a 64-bit key and 22 rounds; its round keys come from a key schedule that reuses the round function with the round index as key. Speck$n$/$m$ denotes block size $n$ and key size $m$.

## Remarks

Each round is invertible: from $(x',y')=R_K(x,y)$ one gets $y=(x'\oplus y')\ggg\beta$ and then $x=((x'\oplus K)\boxminus y)\lll\alpha$, matching the displayed inverse. The only nonlinear operation is the modular addition, whose XOR-differential behaviour determines the cipher's differential properties. The test vector for Speck32/64 in the specification is key 1918 1110 0908 0100, plaintext 6574 694c, ciphertext a868 42f2.

## Depends on

- [Block cipher (uniform family)](../block-ciphers-and-strong-prps/block-cipher.md)

## Proof depends on

None.

## Sources

- Ray Beaulieu, Douglas Shors, Jason Smith, Stefan Treatman-Clark, Bryan Weeks, Louis Wingers, "The SIMON and SPECK Families of Lightweight Block Ciphers", IACR ePrint 2013/404, Section 4.1, [https://eprint.iacr.org/2013/404](https://eprint.iacr.org/2013/404) and Appendix C (test vectors).
- Ray Beaulieu, Douglas Shors, Jason Smith, Stefan Treatman-Clark, Bryan Weeks, Louis Wingers, "Simon and Speck: Block Ciphers for the Internet of Things", NIST Lightweight Cryptography Workshop 2015, [https://csrc.nist.gov/csrc/media/events/lightweight-cryptography-workshop-2015/documents/papers/session1-shors-paper.pdf](https://csrc.nist.gov/csrc/media/events/lightweight-cryptography-workshop-2015/documents/papers/session1-shors-paper.pdf), Section 3 (round function and rotation amounts) and Table 1 (round counts).
- Aron Gohr, "Improving Attacks on Round-Reduced Speck32/64 Using Deep Learning", CRYPTO 2019, Lecture Notes in Computer Science 11693, pp. 150–179, https://doi.org/10.1007/978-3-030-26951-7_6; numbers from IACR ePrint 2019/037, [https://eprint.iacr.org/2019/037](https://eprint.iacr.org/2019/037), Section 2.2, Equation (2).
- Adrien Benamira, David Gerault, Thomas Peyrin, Quan Quan Tan, "A Deeper Look at Machine Learning-Based Cryptanalysis", EUROCRYPT 2021, Lecture Notes in Computer Science 12696, https://doi.org/10.1007/978-3-030-77870-5_28 (conference version, [https://iacr.org/archive/eurocrypt2021/126960385/126960385.pdf](https://iacr.org/archive/eurocrypt2021/126960385/126960385.pdf)), Section 2.1 and Figure 1.
