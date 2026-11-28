# In the two-loss example, VaR of the sum is 100

At level `0.95`, the total loss `L₁ + L₂` of the two independent losses (each 100 with
probability 0.04, else 0) has `VaR_0.95 = 100`: its distribution function is at most
`0.9216 < 0.95` below `100` and at least `0.9984 ≥ 0.95` from `100` on, so
`{x : 0.95 ≤ F(x)} = [100, ∞)`, whose infimum is `100`.
