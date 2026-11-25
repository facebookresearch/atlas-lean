# Comm Hopf Alg Cat Op Equiv Affine Group Scheme Cat

`Spec` as an anti-equivalence from commutative `S`-Hopf algebras onto affine group
schemes over `Spec S`. The underlying functor is Mathlib's `AlgebraicGeometry.hopfSpec`,
which is fully faithful with essential image the affine group schemes; the isomorphism
`commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso` records this on the level
of functors, and is the intended interface for computing with the equivalence.
