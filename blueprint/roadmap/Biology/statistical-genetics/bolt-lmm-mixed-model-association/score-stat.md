# Score statistic for one SNP

The score statistic `(xᵀ P y)² / (xᵀ P x)` for one SNP `x`. Its denominator is positive
when `x` is not in the column space of `X` (`info_pos`); otherwise the statistic is `0` by
the convention `a / 0 = 0` and carries no information.
