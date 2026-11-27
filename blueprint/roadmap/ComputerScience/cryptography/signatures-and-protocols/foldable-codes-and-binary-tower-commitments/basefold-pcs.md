# BaseFold: field-agnostic multilinear polynomial commitments

For any foldable code family with constant relative minimum distance (in particular Reed–Solomon over FFT-friendly fields and random foldable codes over arbitrary sufficiently large fields), there is an IOPP for the code and, by combining it with sum-check through the folding–evaluation link, a multilinear polynomial commitment scheme in the random oracle model (via Merkle commitments and the BCS transform) with prover time $O(n\log n)$ field operations and hashes for $n$ coefficients and verifier time and proof size $O(\lambda\log^{2}n)$ hashes and field elements. Knowledge soundness holds in the unique-decoding regime with soundness error decreasing exponentially in the number of queries.

## Proof sketch

The IOPP folds the committed word $d$ times with verifier challenges and checks consistency of adjacent layers at random positions, as in FRI. Distance preservation under folding follows from a proximity-gap argument for foldable codes in the unique-decoding regime. Sharing challenges with the sum-check on $\bar{m}\cdot\widetilde{\mathrm{eq}}(z,\cdot)$ yields evaluation proofs.

## Depends on

- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Foldable linear codes](foldable-linear-code.md)

## Proof depends on

- [Folding a foldable encoding computes a multilinear evaluation](basefold-evaluation-link.md)
- [Reed–Solomon codes on smooth multiplicative domains are foldable](rs-is-foldable.md)
- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)

## Sources

- Hadas Zeilberger, Binyi Chen, Ben Fisch, "BaseFold: Efficient Field-Agnostic Polynomial Commitment Schemes from Foldable Codes", CRYPTO (2024), IACR ePrint 2023/1705.
