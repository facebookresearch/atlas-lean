# Poisson mass of the states with total count n

Let `S` be a finite set, `c ∈ ℝ^S` and `n ∈ ℕ`. The [Poisson mass](class-mass.md) of the
[set](total-class.md) of states with total count `n` is
`π_c({x : ∑_s x_s = n}) = (∏_s e^{-c_s}) (∑_s c_s)^n / n!`, by the multinomial theorem. This holds
for every real `c`. Since `∏_s e^{-c_s} = e^{-∑_s c_s}`, for `c ≥ 0` it is the Poisson probability
of `n` with mean `∑_s c_s`: under the [product-form Poisson law](poisson-pmf.md) the total count is
Poisson.
