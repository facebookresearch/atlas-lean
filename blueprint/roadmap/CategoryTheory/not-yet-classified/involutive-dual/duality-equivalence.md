# Duality Equivalence

An involutive contravariant endofunctor is an anti-equivalence.

The inverse of the double-dual isomorphism `ev` plays the role of the counit, and the opposite
of that inverse plays the role of the unit, so unlike `CategoryTheory.Functor.asEquivalence` the
inverse of the resulting equivalence is `F.rightOp`: dualizing back is the same operation as
dualizing.

The body is exposed so that `functor` and `inverse` reduce to `F` and `F.rightOp` outside this
file: the unit and counit computations below only typecheck after that reduction.
