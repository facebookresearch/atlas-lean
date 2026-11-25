# Product-form Poisson law as a probability mass function

Let `S` be a finite set and `c ∈ ℝ^S` with `c_s ≥ 0` for every `s`. The product-form Poisson law
with means `c` is the probability mass function on `ℕ^S` that gives each state `x` the mass
`π_c(x) = ∏_s c_s^{x_s} e^{-c_s} / x_s!`, its
[Poisson weight](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md);
these masses are nonnegative and
[sum to one](../ergodic-theorem-for-complex-balanced-reaction-ne/has-sum-poisson-weight.md). It is
the joint law of independent Poisson counts with means `c_s`, a mean `0` giving the count `0`.
