# Arrhenius rate with a temperature floor

The Arrhenius rate with the temperature floored at `Tfloor / 2`:
`A * exp(-B / max (Tfloor / 2) T)`. It is defined for all real arguments: when
`max (Tfloor / 2) T = 0` the convention `x / 0 = 0` makes it `A`. The intended domain is
`Tfloor > 0`, where the floored temperature is positive.
