# The compensated Bernoulli counting process is a martingale

Assume `∀ n, StronglyMeasurable (ξ n)`, `∀ i ω, ξ i ω = 0 ∨ ξ i ω = 1` and `P[ξ 0] = p`.

With i.i.d. `{0,1}`-valued
increments of mean `p`, the partial sums `∑_{i ≤ k} (ξ i - p)` (counts minus compensator) form
a martingale for the natural filtration of `ξ`. This is the discrete-time martingale whose
diffusive rescaling is `compensatedBernoulliStep`.
