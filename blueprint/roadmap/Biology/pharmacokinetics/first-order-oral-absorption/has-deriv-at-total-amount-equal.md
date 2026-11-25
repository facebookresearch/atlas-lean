# Total amount at equal rates has the budget derivative

For all real `F`, `D`, `ka` and `s`, the total amount `Ag + Ac`, with the
[depot amount](depot-amount.md) `Ag(t) = D * exp (-ka * t)` and the
[equal-rate central amount](central-amount-equal.md) `Ac(t) = F * D * ka * t * exp (-ka * t)`, is
differentiable at `s` with derivative `-(1 - F) * ka * Ag(s) - ka * Ac(s)`.
