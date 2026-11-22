# Linear factor-price relation given a pricing vector

Take finitely many states `ω`, finitely many factors `k` with payoffs `F(k, ω)`, and assets
`a` (finitely or infinitely many) with prices `p(a)` and payoffs `X(a, ω)`. Assume exact factor
spanning, `X(a, ω) = ∑_k b(a, k) F(k, ω)` for every asset `a` and state `ω`, with loadings
`b(a, k)`, and a vector `ψ` on the states (of any sign) that prices every asset:
`p(a) = ∑_ω ψ(ω) X(a, ω)` for every `a`. Then every asset price is the loading-weighted sum of
factor prices, `p(a) = ∑_k b(a, k) π(k)` for every `a`, where `π(k) = ∑_ω ψ(ω) F(k, ω)` is the
`ψ`-value of the payoff of factor `k`; the factors need not be traded. When there are finitely
many assets and at least one state, a strictly positive such `ψ` exists if, for some gross
risk-free return `R > 0`, no portfolio `h` has funded gain `∑_a h(a) (X(a, ω) - R p(a))`
nonnegative in every state and strictly positive in some state.
