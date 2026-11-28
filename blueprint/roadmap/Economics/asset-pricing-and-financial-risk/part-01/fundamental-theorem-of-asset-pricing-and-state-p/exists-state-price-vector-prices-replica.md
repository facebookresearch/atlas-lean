# Without funded arbitrage, positive state prices price every portfolio

Take finitely many states `ω`, at least one, and finitely many assets `a`, where asset `a`
costs `p(a)` today and pays `X(a, ω)` in state `ω`, and a gross risk-free return `R > 0`.
Suppose no portfolio `h` has funded gain `∑_a h(a) (X(a, ω) - R p(a))` nonnegative in every
state and strictly positive in some state. Then there is a state-price vector `ψ` with
`ψ(ω) > 0` for every state and `∑_ω ψ(ω) = 1 / R` that prices every portfolio: for every
`h`, `∑_ω ψ(ω) ∑_a h(a) X(a, ω) = ∑_a h(a) p(a)`. One such vector is `ψ = q / R`, where `q`
is a strictly positive probability vector on the states with `∑_ω q(ω) X(a, ω) = R p(a)` for
every asset, which the fundamental theorem of asset pricing for funded gains provides.
