# Linear factor-price relation under no arbitrage

Take finitely many states `ω`, at least one, finitely many assets `a` with prices `p(a)` and
payoffs `X(a, ω)`, and finitely many factors `k` with payoffs `F(k, ω)`, and assume exact
factor spanning: `X(a, ω) = ∑_k b(a, k) F(k, ω)` for every asset `a` and state `ω`. Suppose
that, for some gross risk-free return `R > 0`, no portfolio `h` has funded gain
`∑_a h(a) (X(a, ω) - R p(a))` nonnegative in every state and strictly positive in some state.
Then there is a state-price vector `ψ` with `ψ(ω) > 0` for every state and
`∑_ω ψ(ω) = 1 / R` such that, with the factor prices `π(k) = ∑_ω ψ(ω) F(k, ω)` (the
`ψ`-values of the factor payoffs), every asset price is the loading-weighted sum of factor
prices: `p(a) = ∑_k b(a, k) π(k)` for every asset `a`.
