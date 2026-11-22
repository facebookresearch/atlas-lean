# Hedge Ratio

The delta-hedging ratio for horizon `N` at history `s` (time `s.length < N`): the number of
shares held over the next period, the change in claim value divided by the change in stock price
across the two successor nodes. It depends only on the history up to now (nonanticipating).
