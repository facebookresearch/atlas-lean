# Dual witness for the AC power flow relaxation

For `n_N` buses, `n_E` branches and a width `k`, an AC dual witness consists of real multipliers for
the upper and lower active-generation limits, the upper and lower reactive-generation limits and the
upper and lower squared-voltage limits at every bus, a real multiplier for the squared-current limit
of every branch, and a complex `n_N × k` factor `F`. Nonnegativity of the multipliers
([sign check](nonneg.md)) and the factorization `S = F Fᴴ` of the [dual slack](dual-slack.md) are
not part of the structure; the results assume them separately.
