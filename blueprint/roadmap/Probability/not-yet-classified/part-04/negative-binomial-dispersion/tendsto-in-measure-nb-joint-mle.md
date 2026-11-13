# Consistency of the joint `(β, θ)` maximum likelihood estimator, under explicit hypotheses

Let `K` be a compact parameter set of pairs `(β, θ)` (the shape `θ` is estimated) and let `M` be a
population criterion (typically the expected log mass function) such that

* (positive shapes) every `p ∈ K` has `0 < p.2`: `nbLogPmf` is identified
  with the negative-binomial log mass function only for `θ > 0`, so without
  this the maximizer could lie at an invalid shape (e.g. `θ = 0`);
* (continuity) `M` is continuous on `K`;
* (identifiability) `p₀ ∈ K` is the unique maximizer of `M` on `K`;
* (uniform law of large numbers) the averaged joint log-likelihood `nbAvgLogLik` converges to `M`
  uniformly on `K` in probability;
* (estimator) `p̂ n` lies in `K` with probability tending to one, and for every `δ > 0` its
  averaged log-likelihood is at least the value at `p₀` minus `δ` with probability tending to one
  (an exact maximizer over `K` qualifies).

Then `p̂ n → p₀` in probability. None of the three conditions is derived from a sampling model
here; in particular the uniform LLN and the identification of `p₀` as the maximizer of the
expected log-likelihood are hypotheses. The probabilities of the possibly non-measurable events are
outer measures, so no measurability of `p̂` is needed.
