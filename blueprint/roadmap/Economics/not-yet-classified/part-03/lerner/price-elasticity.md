# Price Elasticity

Price elasticity of demand at output `q` in reciprocal-slope form, from the inverse demand `P`
and a slope `P'`: `ε = P(q) / (q P')`. The definition imposes no relation between `P'` and `P`;
`lerner_of_isLocalMax` requires `HasDerivAt P P' q`. It equals the usual `(dq/dp) (p/q)` only
when demand has a local inverse `p ↦ q(p)` near `q` differentiable with derivative `1 / P'` (for
example, by the inverse function theorem when `P` is continuously differentiable near `q` with
`P' ≠ 0`); no such assumption is made here.
