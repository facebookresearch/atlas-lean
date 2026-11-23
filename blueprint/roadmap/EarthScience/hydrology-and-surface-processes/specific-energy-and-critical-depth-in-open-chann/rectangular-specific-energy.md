# Rectangular Specific Energy

Specific energy per unit weight for a rectangular channel at
depth `h`, with discharge per unit width `q` and gravity `g`:
depth plus velocity head, `h + q^2 / (2 * g * h^2)`. Physically
meaningful for `0 < g` and `0 < h`; outside that range the formula
uses Lean's totalized division.
