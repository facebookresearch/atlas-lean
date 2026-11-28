# The Lorentzian ansatz manifold is invariant and closes on the order parameter

**The Lorentzian ansatz manifold is invariant and closes on the order parameter** (Ott and
Antonsen 2008, Sections III and IV.b and Eq. (14)). Let `K, Λ, Ω, ω₀` be real and let `α₀` lie in
the strict-real-boundary subclass `Admissible` of their invariant manifold (modulus `< 1` on the
real axis, where the manifold allows modulus `≤ 1`). Then there is a solution `r` of the
order-parameter equation (14) (`r' = orderField K Λ Ω ω₀ r`, derivative within `[0, ∞)` at every
`t ≥ 0`, one-sided at `0`) on `[0, ∞)` with `r 0 = conj (α₀ (ω₀ - i))`, such that:
* there is a family `α(w, t)` that, for each `w` with `Im w ≤ 0`, solves the ansatz equation
  `α(w, ·)' = ansatzField Ω w (K r(t) + Λ) α(w, ·)` on `[0, ∞)` (derivative within `[0, ∞)` at
  every `t ≥ 0`, one-sided at `0`) with `α(w, 0) = α₀ w`; and
* every such family satisfies, for every `t ≥ 0`: `α(·, t)` stays in the subclass `Admissible`,
  and `conj (r t) = ∫ α(ω, t) g_L(ω) dω` for the Lorentzian density `g_L = cauchyPDFReal ω₀ 1`
  with `Δ = 1` centred at `ω₀` (self-consistency, Eq. (7)).

## Sources

- Ott and Antonsen (2008), Sections III and IV.b and Eq. (14).
