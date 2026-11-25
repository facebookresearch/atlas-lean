# Constant volatility

Assume `∀ n i, Measurable (Z n i)`, `Integrable (fun ω => Z 0 0 ω ^ 4) μ`, `Measurable K`, `∀ k, Measurable (τ k)`, `∀ k, Measurable (ξ k)` and `∀ᵐ ω ∂μ, Set.InjOn (fun k => τ k ω) (Finset.range (K ω))`.

On the grid of mesh `1/n` of `[0, 1]`, with continuous increments
`σ / √n * Z n i` (each row `Z n` i.i.d. with the law of `Z 0 0`, finite fourth moment) plus
finitely many jumps at a.s. distinct times, the bipower variation over the `n` increments tends
to `(E|Z 0 0|)² σ²` in probability.
