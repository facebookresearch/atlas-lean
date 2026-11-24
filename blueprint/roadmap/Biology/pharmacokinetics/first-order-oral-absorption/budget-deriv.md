# Derivative of the total amount at distinct rates

For distinct rates `ka ≠ k` and all real `F`, `D` and `t`, the total amount `Ag + Ac`, with the
[depot amount](depot-amount.md) `Ag(t) = D * exp (-ka * t)` and the
[distinct-rate central amount](central-amount.md)
`Ac(t) = F * D * ka * (exp (-k * t) - exp (-ka * t)) / (ka - k)`, has at `t` the derivative
`-(1 - F) * ka * Ag(t) - k * Ac(t)`: the absorption loss plus the central elimination.
