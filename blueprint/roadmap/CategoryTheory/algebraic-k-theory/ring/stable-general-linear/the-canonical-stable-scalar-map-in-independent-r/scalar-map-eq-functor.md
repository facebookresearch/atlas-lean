# Scalar Map eq functor

For semirings `R`, `S` in the same universe and `f : R →+* S`,
`scalarMap f` is the group homomorphism underlying
`StableGL.functor.map (SemiRingCat.ofHom f)`. The definition of `scalarMap` itself does
not require the universes to match.
