# Law of one price given a pricing vector

Take finitely many states `ω` and finitely many assets `a`, where asset `a` has price `p(a)`
and pays `X(a, ω)` in state `ω`. Suppose a vector `ψ` on the states (of any sign) prices every
asset: `p(a) = ∑_ω ψ(ω) X(a, ω)` for every `a`. Then two portfolios `h` and `h'` with the same
payoff in every state, `∑_a h(a) X(a, ω) = ∑_a h'(a) X(a, ω)` for every `ω`, have the same
price: `∑_a h(a) p(a) = ∑_a h'(a) p(a)`. A strictly positive such `ψ` exists when there is at
least one state and, for some gross risk-free return `R > 0`, no portfolio `h` has funded gain
`∑_a h(a) (X(a, ω) - R p(a))` nonnegative in every state and strictly positive in some state.
