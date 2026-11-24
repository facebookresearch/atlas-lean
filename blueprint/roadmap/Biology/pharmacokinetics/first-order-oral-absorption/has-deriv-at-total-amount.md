# Total amount at distinct rates has the budget derivative

For distinct rates `ka ≠ k` and all real `F`, `D` and `s`, the total amount `Ag + Ac`, with the
[depot amount](depot-amount.md) `Ag(t) = D * exp (-ka * t)` and the
[distinct-rate central amount](central-amount.md)
`Ac(t) = F * D * ka * (exp (-k * t) - exp (-ka * t)) / (ka - k)`, is differentiable at `s` with
derivative `-(1 - F) * ka * Ag(s) - k * Ac(s)`.
