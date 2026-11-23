# Storage stays within a capacity bounding initial and steady storage

Let `k > 0` be the recession coefficient, `I` the inflow, `S0` the initial storage and `Smax` a
capacity with `S0 ≤ Smax` and `I / k ≤ Smax`. Then at every time `t ≥ 0` the linear-reservoir
storage satisfies `I / k + (S0 - I / k) * exp (-k * t) ≤ Smax`.
