# A matching conditional mean solves the population rate equation

Let `μ` be a probability measure on `Ω`, `S : Ω → ℝ` measurable with `S(ω) > 0` for every `ω`, and
`K : Ω → ℕ` measurable and integrable. Let `a₀` be real and `b₀ > 0`, and assume
`E[K g(S)] = (a₀ / b₀) E[S g(S)]` for every measurable `g : ℝ → ℝ` with `|g(x)| ≤ 1` for all `x`
(expectations are Bochner integrals, `0` for a non-integrable integrand). Then the
[population rate score](pop-rate-score-log.md) vanishes at `(a₀, b₀)`:
`R(a₀, b₀) = a₀ - E[(a₀ + K) b₀ / (b₀ + S)] = 0`.

The assumption holds, for example, when `E[K ∣ S] = a₀ S / b₀` almost surely, as in the hierarchy
`K ∣ S, λ ~ Po(S λ)` with `λ ~ Gamma(a₀, b₀)` independent of `S`.
