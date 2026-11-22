# Pointwise ladder commutator for Schwartz functions

Pointwise ladder identity for Schwartz functions:
`annFun (creFun f) x - creFun (annFun f) x = f x` for every `f` in `SchwartzCarrier` (Mathlib
`SchwartzMap.smooth`, `ContDiff.deriv`). This is the identity of the differential
expressions `annFun` and `creFun`; `annihilation_creation_commutator` states it for the
records `annihilation` and `creation`.
