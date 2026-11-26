# LatticeFold+: algebraic range proofs and double commitments for lattice folding

Assuming Module-SIS over a power-of-two cyclotomic ring, there is a lattice-based folding scheme for linear and rank-1/CCS relations with Ajtai commitments in which norm control is achieved by a purely algebraic range proof (encoding small integers as monomials and certifying monomiality, with values recovered by constant-term extraction) instead of bit decomposition, and in which proofs are shortened by double commitments folded via a sum-check-based transformation. Compared with LatticeFold, the prover is faster, the verification circuit simpler and the folding proofs shorter, with knowledge soundness under Module-SIS and plausible post-quantum security.

## Proof sketch

Monomial encoding turns range constraints into multiplicative relations checkable by sum-check with low degree; constant-term extraction links them back to integer values. Double commitments compress the many commitments created by decomposition, and binding reduces to Module-SIS for both layers. Extraction combines sum-check soundness and challenge-difference invertibility as in LatticeFold.

## Depends on

- [LatticeFold: post-quantum folding for CCS from Module-SIS](latticefold-theorem.md)
- [Constant-term extraction of exponents in the negacyclic ring](monomial-constant-term-range.md)
- [Binding of double commitments under Module-SIS](double-commitments.md)

## Proof depends on

- [Constant-term extraction of exponents in the negacyclic ring](monomial-constant-term-range.md)
- [Binding of double commitments under Module-SIS](double-commitments.md)
- [LatticeFold: post-quantum folding for CCS from Module-SIS](latticefold-theorem.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems", CRYPTO (2025), IACR ePrint 2025/247.
