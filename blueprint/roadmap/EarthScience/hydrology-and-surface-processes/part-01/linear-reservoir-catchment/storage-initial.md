# The reservoir storage at time zero is the initial storage

For every inflow `I`, recession coefficient `k` and initial storage `S0` (real numbers), the
linear-reservoir storage `S(t) = I / k + (S0 - I / k) * exp (-k * t)` satisfies `S(0) = S0`. This
includes `k = 0`, where the convention `x / 0 = 0` makes the storage constantly `S0`.
