# Delta-hedging ratio in the binomial tree

For a claim `V`, a horizon `N` and a history `s` of `n` moves, the delta-hedging ratio is the
number of shares held over the next period,
`(v_m(s, up) - v_m(s, down)) / (S(s, up) - S(s, down))` with `m = N - n - 1`: the change in the
backward-induction value of `V` with `m` periods left (discounted risk-neutral averages with
`q = (R - d) / (u - d)`) divided by the change in the stock price `S` (initial price `S₀`, move
factors `u` and `d`, so `S(s, up) = u * S(s)` and `S(s, down) = d * S(s)`) across the two
successor nodes. It is meant for `n < N`; for `n ≥ N` the subtraction `N - n - 1`, taken in the
natural numbers, is truncated to `0`. Division follows the convention x / 0 = 0, so the ratio is
`0` when the two successor prices coincide. It depends only on the history up to now
(nonanticipating).
