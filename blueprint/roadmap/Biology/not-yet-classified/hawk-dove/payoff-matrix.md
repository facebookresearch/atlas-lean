# Hawk–Dove payoff matrix

The row player's payoffs `[[(V - C) / 2, V], [0, V / 2]]` for
the value of the resource `V` and the cost of injury `C`, with rows and columns ordered Hawk
(index `0`), Dove (index `1`). The mixed strategy that plays Hawk with probability `p` is the
vector `(p, 1 - p)`, and its expected payoff `(p, 1 - p) · A (q, 1 - q)` against `(q, 1 - q)` is
`p q (V - C)/2 + p (1 - q) V + (1 - p)(1 - q) V/2`.
