# Fuel consumption of actual stage masses

At a positive exhaust speed `ve`, for a
consumed-fraction functional that consumes nothing on a zero burn, composes burns at `ve`, and
consumes `1 - b / a` on the ideal increment `ve log (a / b)` of a burn from mass `a` to mass
`b ≤ a`, the remaining mass fraction over the burns of admissible stage masses is
`1 - fuel ve (cost)`, the cost being the sum of the stage increments, each nonnegative
(`stageIncrement_nonneg`); jettisoned masses enter no factor. The identity does not use the sign
of `ve`, which restricts the statement to burn costs: at a negative `ve` the premises can hold
while every increment is negative.
