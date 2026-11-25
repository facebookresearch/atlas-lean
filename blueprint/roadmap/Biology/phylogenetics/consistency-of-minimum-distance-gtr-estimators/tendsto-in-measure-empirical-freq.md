# Weak law for pairwise independent columns with a common law

Let `σ` be a finite set of site patterns, every subset of which is measurable. Let `P` be a finite
measure on `Ω` and let the columns `X 0, X 1, …` be measurable maps `Ω → σ` that are pairwise
independent and identically distributed under `P`, with `P (X 0 = a) = q a` for every pattern `a`.
Then the [empirical site-pattern frequencies](empirical-freq.md) `p̂ₙ` converge to `q` in
`P`-measure: for every `ε > 0`, `P {ω : d(p̂ₙ(ω), q) ≥ ε} → 0` as `n → ∞`, where `d` is the sup
distance on `σ → ℝ`. Pairwise independence forces the total mass of `P` to be `0` or `1`, so this is
convergence in probability unless `P` is zero.
