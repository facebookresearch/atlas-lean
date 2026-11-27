# WHIR: IOPP for constrained Reed–Solomon codes with super-fast verification

There is a public-coin IOPP for constrained Reed–Solomon codes $\mathrm{CRS}[\mathbb{F},L,m,\hat{w},\sigma]$ that interleaves sum-check rounds on the constraint with STIR-style rate-shifting iterations (folding by partial evaluation, out-of-domain sampling, and adding the queried points as new constraints rather than quotienting). It is round-by-round sound for proximity parameters up to the unique-decoding radius $(1-\rho)/2$ unconditionally, and up to the Johnson bound $1-\sqrt{\rho}$ assuming the mutual-correlated-agreement conjecture (IACR ePrint 2024/1586, Conjecture 1), where $\rho$ is the rate. For the same code and security parameters its query complexity $q$ is the same as STIR's, and its verifier makes $O(q \cdot (2^k + m))$ field operations, where $k$ is the folding parameter and $m$ the number of variables. Compiled with the BCS transform it gives hash-based multilinear and univariate polynomial commitment schemes and, with a compiler for multilinear PIOPs, a SNARG for generalized R1CS.

## Proof sketch

Each round runs a few sum-check rounds to reduce the constraint, folds the function by partial evaluation (binary-fold lemma), and commits to the folded polynomial on a smaller domain; queried and out-of-domain points become additional weight terms batched into the constraint with random coefficients. Distance preservation follows the STIR analysis with constraints in place of quotients.

## Depends on

- [Constrained Reed–Solomon codes with sum-check constraints](constrained-rs-code.md)
- [STIR: Reed–Solomon proximity testing with O(log d + λ·log log d) queries](stir-theorem.md)
- [Interactive oracle proofs of proximity for Reed–Solomon codes](rs-iopp.md)

## Proof depends on

- [Binary folding of multilinear-coefficient codewords as partial evaluation](whir-binary-fold.md)
- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)
- [One STIR iteration: fold, shift to a smaller domain, quotient](stir-iteration.md)

## Sources

- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification", EUROCRYPT (2025), IACR ePrint 2024/1586.
