# Expected-utility representation of a preference

For a finite set `X` of outcomes and a relation `≿` on lotteries over `X` (probability vectors on
`X`), a function `u : X → ℝ` is an expected-utility (Bernoulli) representation of `≿` when, for all
lotteries `p`, `q`, `p ≿ q ⟺ E_p[u] ≥ E_q[u]`, where `E_p[u] = ∑ₓ p(x) u(x)` (Gonçalves, Definition
1).
