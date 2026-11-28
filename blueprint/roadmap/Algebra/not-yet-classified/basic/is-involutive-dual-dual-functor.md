# Is Involutive Dual dual Functor

Finite dualization is involutive in the sense required to build an anti-equivalence out of
it.

`IsInvolutiveDual` spells the triangle identity with `dualFunctor` and `evalNatIso`; those are
the functor and natural isomorphism assembled from `dualMap` and `evalIso`, so the two forms of
the identity are the same statement and `dualMap_evalIso_inv_comp` applies directly.
