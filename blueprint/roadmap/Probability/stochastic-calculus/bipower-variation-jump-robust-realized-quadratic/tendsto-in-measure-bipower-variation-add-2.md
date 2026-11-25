# Convergence of bipower variation in the presence of jumps

Assume `∀ n i, Measurable (Z n i)`, `∀ n i, IdentDistrib (Z n i) (Z 0 0) μ μ`, `Integrable (fun ω => Z 0 0 ω ^ 4) μ`, `Measurable K`, `∀ k, Measurable (τ k)`, `∀ k, Measurable (ξ k)` and `∀ᵐ ω ∂μ, Set.InjOn (fun k => τ k ω) (Finset.range (K ω))`.

Let the continuous increments
be `s n i * Z n i`, with each row `Z n` independent and every `Z n i` distributed as `Z 0 0`
with finite fourth moment, `∑_{i ≤ L n} (s n i)⁴ → 0` and
`∑_{i < L n} |s n i| |s n (i+1)| → V`, and add the increments of `K` random jumps of sizes `ξ k`
at a.s. distinct times `τ k`. Then the bipower variation tends to `(E|Z 0 0|)² V` in probability:
the jumps do not contribute.
