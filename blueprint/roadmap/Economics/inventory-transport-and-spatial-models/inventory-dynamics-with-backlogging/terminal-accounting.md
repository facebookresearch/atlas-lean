# Terminal stock equals initial stock plus gains minus draws

For resources `i` with initial stocks `s₀(i)` and signed flows `f_i(k)` at steps `k`, the stock
after `t` steps is `s₀(i) + ∑_{k < t} f_i(k)`; the gains are the positive parts `max(f_i(k), 0)` and
the draws the negative parts `max(-f_i(k), 0)`. For every resource `i` and horizon `N`, the stock
after `N` steps is the initial stock plus all gains minus all draws:
`s₀(i) + ∑_{k < N} max(f_i(k), 0) - ∑_{k < N} max(-f_i(k), 0)` (the conservation identity of the
stock-flow model at zero lead time).
