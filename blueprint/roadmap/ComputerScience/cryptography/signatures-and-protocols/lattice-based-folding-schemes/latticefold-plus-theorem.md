# LatticeFold+: algebraic range proofs and double commitments for lattice folding

Assuming Module-SIS over a power-of-two cyclotomic ring, there is a lattice-based folding scheme for linear and rank-1/CCS relations with Ajtai commitments in which norm control is achieved by a purely algebraic range proof (encoding small integers as monomials and certifying monomiality, with values recovered by constant-term extraction) instead of bit decomposition, and in which proofs are shortened by double commitments folded via a sum-check-based transformation. The scheme is complete and knowledge sound under Module-SIS.

## Proof sketch

Monomial encoding turns range constraints into multiplicative relations checkable by sum-check with low degree; constant-term extraction links them back to integer values. Double commitments compress the many commitments created by decomposition, and binding reduces to Module-SIS for both layers. Extraction combines sum-check soundness and challenge-difference invertibility as in LatticeFold.

## Depends on

- [LatticeFold: post-quantum folding for CCS from Module-SIS](latticefold-theorem.md)
- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Proof depends on

- [Constant-term extraction of exponents in the negacyclic ring](monomial-constant-term-range.md)
- [Binding of double commitments under Module-SIS](double-commitments.md)

## Sources

- Dan Boneh, Binyi Chen, "LatticeFold+: Faster, Simpler, Shorter Lattice-Based Folding for Succinct Proof Systems", CRYPTO (2025), IACR ePrint 2025/247.
