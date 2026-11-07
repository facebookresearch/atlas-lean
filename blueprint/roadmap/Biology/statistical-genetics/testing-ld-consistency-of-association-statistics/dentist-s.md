# DENTIST-S statistic

The DENTIST-S statistic `(z_i - r z_c) ^ 2 / (1 - r ^ 2)` of a variant with `z`-score `zi`,
given the `z`-score `zc` of the lead (putative causal) variant and the reference correlation `r`
between them (Kanai et al. 2022, Equation 1). Meaningful for `r ^ 2 < 1`; for `r ^ 2 = 1` it is
`0` by the convention `x / 0 = 0`.
