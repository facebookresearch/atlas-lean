# Front inside: the count rate is the net inflow iff the jump balance

Let `kL`, `kR`, `a`, `b`, `s`, `ξ₀`, `qL`, `qR` and `t` be real, with the front `ξ(t) = s t + ξ₀`
strictly inside the segment at time `t`: `a < s t + ξ₀ < b`. Then the [vehicle count](inventory.md)
`N(t) = kL (ξ(t) - a) + kR (b - ξ(t))` has the derivative `qL - qR` at `t`, the inflow `qL` minus
the outflow `qR`, if and only if the Rankine–Hugoniot balance `s (kR - kL) = qR - qL` holds. For
`kR ≠ kL` this fixes the [front speed](front-speed-eq-of-ne.md).
