# Sex-ratio fitness with unequal costs of sons and daughters

A parent investing a fraction `r'` of its resources in sons, in a population investing a fraction
`r`, when a son costs `cs` and a daughter `cd`, has fitness
`Wcost(cs, cd, r', r) = (r' / cs) / (r / cs) + ((1 - r') / cd) / ((1 - r) / cd)`: its numbers of
sons and of daughters, each relative to the population's. It is defined for all real arguments:
by the convention `a / 0 = 0` the first term is `0` when `cs = 0` or `r = 0`, and the second when
`cd = 0` or `r = 1`. The intended domain is `cs, cd > 0` and `0 < r < 1`.
