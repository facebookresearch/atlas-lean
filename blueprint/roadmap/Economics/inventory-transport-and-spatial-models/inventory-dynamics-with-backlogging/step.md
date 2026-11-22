# One-period transition of stock and pipeline

The deterministic backlogging transition on a state `(I, p)`, a net stock `I ∈ ℝ` and a pipeline
`p = (p_0, …, p_{L-1})` of nonnegative quantities, with order `q ≥ 0` and demand `d ≥ 0`: the
receipt is `r = p_0` if `L > 0` and `r = q` if `L = 0`; the new stock is `I + r - d` (no cap, no
saturation); the new pipeline is `(p_1, …, p_{L-1}, q)`, the old tail followed by `q` (empty when
`L = 0`).
