# Hecke T

The Hecke sum `T_p` in weight `k` on functions on the upper half-plane:
`heckeU k p f + f ∣[k] heckeDiagMatrix p`. With Mathlib's slash action this is
`T_p f τ = p⁻¹ ∑_{j < p} f ((τ + j) / p) + p ^ (k - 1) f (p τ)` for `p ≠ 0` (`heckeT_apply`),
and `T_0 f = f`; it acts on `q`-expansion coefficients by `coeffHeckeT`. On forms of level `N`
it is the classical Hecke operator `T_p` only for a prime `p` not dividing `N`
(`ModularForm.heckeTLin`); for composite `p` it is not `T_p`, and for a prime `p ∣ N` the
classical operator is `heckeU`.
