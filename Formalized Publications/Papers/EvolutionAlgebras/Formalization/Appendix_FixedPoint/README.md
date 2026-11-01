# Appendix: the projective fixed-point principle

The paper cites algebraic geometry for one step of Theorem 3.3 (a
projective fixed point over an algebraically closed field); this appendix
proves it, via a quadratic Bézout argument. It is the largest part of the
formalization.

Reading order:

1. `A_FixedPoint.lean` — the statement of record
   (`fixedPoint_of_idempotent`).
2. `BezoutChain/` — the proof, in five areas: `Statement/` (the statement
   of record and its pieces), `Geometry/` (counting and elimination),
   `Regularity/` (regular sequences, Koszul, multiplicity), `Dimension/`
   (dimension theory), and `BridgeToFixedPoint/` (assembly into the
   fixed-point statement).
3. `AssociatedPrimes/` — supporting associated-prime material.
