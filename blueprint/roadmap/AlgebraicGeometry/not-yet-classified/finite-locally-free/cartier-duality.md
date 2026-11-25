# Cartier duality for finite locally free commutative affine group schemes over an arbitrary commutative base ring

**Cartier duality for finite locally free commutative affine group schemes over an arbitrary
commutative base ring.**

Transporting `FiniteLocallyFreeBicommutativeHopfAlgCat.cartierDuality` rather than the bare
dualization functor keeps the inverse computable: it is again Cartier dualization, and the counit
is the inverse of the double-dual evaluation isomorphism `cartierDualDualIso`.

The body is exposed so that `cartierDuality_inverse` holds definitionally, without which
`cartierDualDualNatIso` does not typecheck.
