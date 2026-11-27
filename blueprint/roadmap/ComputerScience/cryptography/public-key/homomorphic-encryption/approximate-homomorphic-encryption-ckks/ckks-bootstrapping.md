# Bootstrapping for approximate homomorphic encryption

CKKS admits a bootstrapping procedure that, given a level-$0$ ciphertext of $m$ (with $\|m\|_\infty\le\epsilon q_0$ coefficientwise), outputs a ciphertext at a higher level $L-L_{\mathrm{boot}}$ encrypting $m$ up to a small additional error. It consists of: ModRaise to modulus $q_L$, yielding $m+q_0I$; CoeffToSlot, a homomorphic evaluation of the inverse canonical embedding (a linear transform realized by rotations and plaintext multiplications, decomposable in $O(\log N)$ sparse FFT-like levels) moving coefficients into slots; EvalMod, evaluating the scaled sine approximation of reduction modulo $q_0$ slotwise via a polynomial approximation and double-angle iterations; and SlotToCoeff, the forward transform. Assuming Ring-LWE and circular security of the evaluation keys, this yields fully homomorphic approximate arithmetic over complex vectors, with precision loss controlled by $\epsilon^{2}$ from the sine approximation and by the polynomial approximation error.

## Proof sketch

Correctness composes the ModRaise lemma, the linear-transform correctness of CoeffToSlot and SlotToCoeff (rotations via Galois automorphisms), and the sine-approximation lemma for EvalMod, together with approximate correctness of CKKS evaluation for the polynomial approximation; the error terms add. Levels consumed are independent of the original computation.

## Depends on

- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)
- [CKKS encoding via the canonical embedding](canonical-embedding-encoding.md)

## Proof depends on

- [ModRaise introduces a small integer multiple of the base modulus](ckks-modraise.md)
- [Approximating modular reduction by a scaled sine](sine-mod-approximation.md)
- [Approximate correctness of CKKS homomorphic evaluation](ckks-approximate-correctness.md)
- [Gentry's bootstrapping theorem](../gentry-s-bootstrapping-theorem.md)

## Sources

- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "Bootstrapping for Approximate Homomorphic Encryption", EUROCRYPT (2018).
