# Jump robustness of bipower variation

Assume `Measurable K`, `∀ k, Measurable (τ k)`, `∀ k, Measurable (ξ k)` and `∀ᵐ ω ∂μ, Set.InjOn (fun k => τ k ω) (Finset.range (K ω))`.

Let `c n i` be continuous increments whose largest
one, over the `L n + 1` increments used, tends to `0` in probability, and add the increments of
`K` random jumps of sizes `ξ k` at a.s. distinct times `τ k`. Then the bipower variation changes
by an amount tending to `0` in probability.
