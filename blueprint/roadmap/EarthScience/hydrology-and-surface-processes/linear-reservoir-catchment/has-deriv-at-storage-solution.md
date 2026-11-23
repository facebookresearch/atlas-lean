# The storage profile solves the linear-reservoir equation

For a recession coefficient `k > 0` and any real inflow `I` and initial storage `S0`, the storage
`S(t) = I / k + (S0 - I / k) * exp (-k * t)` is differentiable at every real time `t`, with
derivative `S'(t) = I - k * S(t)`.
