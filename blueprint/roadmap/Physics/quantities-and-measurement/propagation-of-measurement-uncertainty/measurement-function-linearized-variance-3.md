# First-order law of propagation, uncorrelated inputs

Let `X i` (`i ∈ ι`, a finite index set) be real random variables with finite second moments on a
probability space. If `f` has derivative `f'` at `x`, the inputs have standard uncertainties `u i`
(`Var[X i] = u i ^ 2`) and are pairwise uncorrelated (`cov[X i, X j] = 0` for `i ≠ j`), then the
variance of the linearization `ω ↦ f x + f' (X ω - x)` is `∑ i, (∂f/∂xᵢ (x) * u i) ^ 2`. Only
`u i ^ 2` enters, so the sign convention `0 ≤ u i` is not needed. Pairwise independent inputs are
uncorrelated.
