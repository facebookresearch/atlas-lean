# Consistency of a root of a cluster estimating equation

**Consistency of a root of a cluster estimating equation** (Z-estimator consistency).

Let `U i β ω` be the score of cluster `i` at parameter `β`. Suppose that, on a compact parameter
set `K`,

* (uniform convergence) the averaged estimating function `n⁻¹ • ∑_{i<n} U i β` converges to a
  deterministic `g β` uniformly on `K` in probability,
* (identifiability) `g` is continuous on `K` and `β₀` is its only zero in `K`,
* (root in the neighbourhood) the estimator `βhat n` lies in `K` and solves the estimating
  equation `∑_{i<n} U i (βhat n) = 0`, each with probability tending to one.

Then `βhat n → β₀` in probability. The probabilities of the possibly non-measurable events
are outer measures, so no measurability of `βhat` or of the supremum is needed.
