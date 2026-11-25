# In the two-loss example, VaR of the second loss is 0

At level `0.95`, the second loss `L₂` (100 with probability 0.04, else 0, under the product
weights) has `VaR_0.95 = 0`: its distribution function is `0 < 0.95` below `0` and at least
`0.96 ≥ 0.95` from `0` on, so `{x : 0.95 ≤ F(x)} = [0, ∞)`, whose infimum is `0`.
