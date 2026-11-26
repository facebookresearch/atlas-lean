# Restriction of an over-site module morphism

Let `S : Type u` be a topological space, `R` a ring sheaf of carrier universe `v`, and `M,N`
module sheaves with a common carrier universe `w`. For an inclusion `i : U → V` and `h :
M.over V → N.over V`, `overHomRestrict i h : M.over U → N.over U` is `((overFunctorMap R
i).app M).inv ≫ (overMap R i).map h ≫ ((overFunctorMap R i).app N).hom`, using the canonical
over-site comparisons. The universes `u,v,w` are independent.
