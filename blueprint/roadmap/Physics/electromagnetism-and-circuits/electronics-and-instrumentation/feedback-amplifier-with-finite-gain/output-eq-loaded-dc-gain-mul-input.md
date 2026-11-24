# Loaded DC gain of the signal model

At `s = 0`, with `wp ≠ 0`
and `1 + beta * b * A0 ≠ 0`, any unloaded and loaded output signals
obeying the two model equations satisfy
`vo = loadedDcGain A0 beta a b * vi`. The open-loop denominator is
`1` at `s = 0`, the loaded denominator reduces to
`1 + beta * b * A0`, and the transfer theorem then applies.
