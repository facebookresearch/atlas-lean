# For each total n, the conditioned law is the multinomial mass function

Let `S` be a finite set, `c ∈ ℝ^S` with `c_s > 0` for every `s`, and `n ∈ ℕ`. The
[law conditioned](conditioned-law.md) on the [set](total-class.md) of states with total count `n`
is, as a function on `ℕ^S`, the
[multinomial mass function](../../../Probability/distributions/discrete/multinomial-distribution/multinomial-real.md)
with `n` throws and cell probabilities `p_s = c_s / ∑_{s'} c_{s'}`: `π_c(x | ∑ = n) = M_n(p; x)` for
every `x ∈ ℕ^S`. Both vanish off `{x : ∑_s x_s = n}`, and on it they agree by the
[multinomial formula](conditioned-law-total-class.md). For nonempty `S`, `p` is a probability vector
and this is the multinomial distribution of `n` throws. For empty `S` and `n ≥ 1` no state has total
`n`, and both sides are `0`, the conditioned law by the convention `y / 0 = 0`.
