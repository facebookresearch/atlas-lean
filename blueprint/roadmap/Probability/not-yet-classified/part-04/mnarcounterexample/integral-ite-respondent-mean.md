# Mean imputation estimates the respondents' mean

Filling every missing outcome with the
respondents' mean `m = E[Y 1_R] / P(R)` gives a completed outcome whose mean is `m` itself. Since
`m` is a functional of the observed-data law, `exists_map_obsRY_eq_integral_ne` shows that it is
the full-data mean only under an assumption on the nonresponse mechanism.
