# Expected utility of a lottery

A lottery over a finite set `X` of outcomes is a probability vector `p` on `X` (a point of the
standard simplex: `p(x) ≥ 0` for every outcome and `∑ₓ p(x) = 1`). Its expected utility under a
Bernoulli utility `u : X → ℝ` is `E_p[u] = ∑ₓ p(x) u(x)` (Gonçalves, Definition 1).
