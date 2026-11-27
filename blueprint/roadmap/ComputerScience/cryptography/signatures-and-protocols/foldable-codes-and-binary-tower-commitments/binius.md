# Binius: succinct arguments over towers of binary fields

There is a multilinear polynomial commitment scheme for polynomials with coefficients in a small tower field $\mathcal{T}_\iota$ (down to $\mathbb{F}_2$), built from a Reed–Solomon code over a larger tower field $\mathcal{T}_\tau$ evaluated by the additive FFT, with packing of $2^{\tau-\iota}$ coefficients per encoded symbol and Merkle hashing, adapting the Brakedown polynomial commitment scheme. Its commitment cost is proportional to the total bit-length of the committed data rather than to the number of coefficients times a large field size, and, as in Brakedown, proof size and verifier work grow with the square root of the polynomial's size: for each fixed $\iota$, a polynomial in $\ell$ variables has verifier cost $\widetilde{O}(\sqrt{\lambda\cdot 2^{\ell}})$, counting both bits transferred and bit operations. Combined with sum-check-based PIOPs (zero-checks, product and lookup arguments) over the tower, it yields SNARKs for binary-native computations such as bitwise hash functions. A later variant of the commitment, by the same authors, replaces Brakedown with a characteristic-$2$ adaptation of the FRI-style BaseFold commitment, combined with a sum-check-based ring-switching reduction, and has polylogarithmic proofs.

## Proof sketch

Packing lets one encoding symbol over $\mathcal{T}_\tau$ carry many small-field coefficients, so committing costs one encoding per $2^{\tau-\iota}$ coefficients. Evaluation claims over the extension field are reduced to claims about the packed polynomial by a tensor-product structure of the multilinear basis. Soundness follows from proximity testing of the code and sum-check soundness over a sufficiently large extension field.

## Depends on

- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Wiedemann towers of binary fields](binary-tower.md)

## Proof depends on

- [Packing small-field elements into tower-field elements](tower-packing.md)
- [Additive FFT in the novel polynomial basis](additive-fft.md)
- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)

## Sources

- Benjamin E. Diamond, Jim Posen, "Succinct Arguments over Towers of Binary Fields", EUROCRYPT (2025), IACR ePrint 2023/1784, Construction 3.11 and Theorem 3.14.
- Benjamin E. Diamond, Jim Posen, "Polylogarithmic Proofs for Multilinears over Binary Towers", EUROCRYPT (2026), IACR ePrint 2024/504.
