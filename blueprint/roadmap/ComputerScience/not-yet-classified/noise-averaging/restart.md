# Restarted recursion

`restart α w t₀ n` is the recursion
`W (t + 1) = (1 - α t) * W t + α t * w t` started from `0` at time `t₀` and evaluated at time
`t₀ + n`: the process `W(t; t₀)` of Tsitsiklis (1994, p. 192) at `t = t₀ + n`.
