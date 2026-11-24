# Saddle-node bifurcation in b

Let `a > 0` and `b₀ > 0`, and let `(u₀, v₀)` be an [equilibrium](is-equilibrium.md) of the toggle
switch with Hill exponents `β = 1`, `γ = 2` and rates `a = α₁`, `α₂ = b₀`, with
[tangent nullclines](nullclines-tangent.md) at `(u₀, v₀)` and `3u₀ ≠ a`; put `d = 3u₀ − a`. Then:

- there is `η > 0` such that for every `b > 0` with `(b − b₀) d > 0`, every equilibrium `(u, v)`
  of the system with rate `b` has `|u − u₀| ≥ η`;
- for every `δ > 0` there is `ε > 0` such that for every `b > 0` with `|b − b₀| < ε` and
  `(b₀ − b) d > 0`, the system with rate `b` has two equilibria `(u₁, b / (1 + u₁²))` and
  `(u₂, b / (1 + u₂²))` with `u₁ < u₀ < u₂`, `|u₁ − u₀| < δ` and `|u₂ − u₀| < δ`.

So as `b` tends to `b₀` from the side `(b₀ − b) d > 0`, two equilibria approach `u₀`, and on the
other side none is near `u₀`. Which of the two is the saddle is not stated.
