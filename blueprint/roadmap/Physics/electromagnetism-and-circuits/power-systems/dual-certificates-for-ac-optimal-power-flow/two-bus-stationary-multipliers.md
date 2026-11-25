# Stationarity multipliers at the two-bus stationary voltage

The multipliers for the [two-bus example](two-bus-cert-example.md) with value `4` on the lower
active limit at bus `1`, `-25/16` on the upper squared-voltage limit at bus `0` and `0` elsewhere,
packaged as an [AC dual witness](acdual-certificate.md) with factor `0` (unused). The negative
multiplier fails the [sign check](nonneg.md). Their dual slack annihilates the voltage `(2, 3/4)`
([checks](two-bus-stationary-point-not-certificate.md)).
