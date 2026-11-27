# Crude RR

The crude risk ratio `P(Y = 1 | E = 1) / P(Y = 1 | E = 0)`. It is meaningful when `0 < Pe < 1`
and the risk among the unexposed is positive; a zero denominator gives `0` by Lean's convention
`x / 0 = 0`.
