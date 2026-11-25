# Derivative of the total amount at equal rates

For all real `F`, `D`, `ka` and `t`, the total amount `Ag + Ac`, with the
[depot amount](depot-amount.md) `Ag(t) = D * exp (-ka * t)` and the
[equal-rate central amount](central-amount-equal.md) `Ac(t) = F * D * ka * t * exp (-ka * t)`, has
at `t` the derivative `-(1 - F) * ka * Ag(t) - ka * Ac(t)`.
