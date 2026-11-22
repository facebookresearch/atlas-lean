# No arbitrage on funded gains

Take finitely many states `ω` and finitely many assets `a`, where asset `a` costs `p(a)`
today and pays `X(a, ω)` in state `ω`, and a gross risk-free return `R` (any real number).
Buying `h(a)` units of asset `a` with money borrowed at `R` has funded gain
`h(a) (X(a, ω) - R p(a))` in state `ω`, so a portfolio `h` (any real vector indexed by the
assets, short positions allowed) has funded gain `∑_a h(a) (X(a, ω) - R p(a))`. The market
has no arbitrage on funded gains when no portfolio has a funded gain that is nonnegative in
every state and strictly positive in some state.
