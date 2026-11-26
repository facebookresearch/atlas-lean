# Weighted mean over an event

For a real weight `P` on full assignments, an event `E`, a node `y` and a real function `g`, the
ratio `(∑_{v ∈ E} P(v) g(v_y)) / P(E)` of the `P`-weighted sum of `g` at node `y` over `E` to the
weight `P(E)` of `E`. When `P(E) = 0` the value is `0`, by the convention `a / 0 = 0`. When `P` is a
probability law and `P(E) > 0`, it is the conditional mean `E(g(X_y) | E)`.
