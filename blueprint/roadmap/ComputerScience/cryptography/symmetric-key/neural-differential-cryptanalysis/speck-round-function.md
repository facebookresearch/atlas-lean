# The Speck round function

Speck is an ARX block cipher family: on two $k$-bit words, a round maps $(x,y)$ to $\bigl((x\ggg\alpha)\boxplus y)\oplus K,\ (y\lll\beta)\oplus((x\ggg\alpha)\boxplus y)\oplus K\bigr)$, with $(\alpha,\beta)=(7,2)$ for Speck32/64, which has 22 rounds.

Fix a word size $k$ and rotation amounts $\alpha,\beta$. For a round key $K\in\{0,1\}^k$ the Speck round function on a state of two $k$-bit words $(x,y)$ is

$$
R_K(x,y)=\bigl(((x\ggg\alpha)\boxplus y)\oplus K,\ \ (y\lll\beta)\oplus((x\ggg\alpha)\boxplus y)\oplus K\bigr),
$$

where $\boxplus$ is addition modulo $2^k$, $\oplus$ is bitwise exclusive or, and $\ggg,\lll$ are rotations right and left. Equivalently, with $(L_i,R_i)$ the state, $L_{i+1}=((L_i\ggg\alpha)\boxplus R_i)\oplus K_i$ and $R_{i+1}=(R_i\lll\beta)\oplus L_{i+1}$. The amounts are $\alpha=7$, $\beta=2$ when the block size is $32$ ($k=16$), and $\alpha=8$, $\beta=3$ otherwise.

**Speck32/64** has a 32-bit block, a 64-bit key and 22 rounds; its round keys come from a key schedule that reuses the round function with the round index as key. Speck$n$/$m$ denotes block size $n$ and key size $m$.

## Remarks

Each round is invertible: from $(x',y')=R_K(x,y)$ one gets $y=(x'\oplus y')\ggg\beta$ and then $x=((x'\oplus K)\boxminus y)\lll\alpha$, so $R_K^{-1}(x,y)=\bigl(((x\oplus K)\boxminus((x\oplus y)\ggg\beta))\lll\alpha,\ (x\oplus y)\ggg\beta\bigr)$, with $\boxminus$ subtraction modulo $2^k$. The designers note that Speck gets its nonlinearity from the modular addition.

## Depends on

- [Block cipher (uniform family)](../block-ciphers-and-strong-prps/block-cipher.md)

## Proof depends on

None.

## Sources

- Ray Beaulieu, Douglas Shors, Jason Smith, Stefan Treatman-Clark, Bryan Weeks, Louis Wingers, "Simon and Speck: Block Ciphers for the Internet of Things", NIST Lightweight Cryptography Workshop 2015, [https://csrc.nist.gov/csrc/media/events/lightweight-cryptography-workshop-2015/documents/papers/session1-shors-paper.pdf](https://csrc.nist.gov/csrc/media/events/lightweight-cryptography-workshop-2015/documents/papers/session1-shors-paper.pdf), Section 3 (round function, rotation amounts, key schedule) and Table 1 (round counts).
