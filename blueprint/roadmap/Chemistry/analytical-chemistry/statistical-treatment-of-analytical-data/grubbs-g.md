# Grubbs G

Grubbs' statistic `G = max_i |x i - x̄| / s` of a sample: the largest absolute deviation from
the sample mean over the sample standard deviation, and `0` when `s = 0` (no spread, hence no
rejection). The maximum is over the whole sample (`div_le_grubbsG`) and is attained by an
observation (`exists_grubbsG_eq`). Grubbs' procedure needs at least three observations
(`grubbsReject` requires it); for two distinct observations `G = 1/√2` whatever the data.
Tabulated critical values assume i.i.d. normal sampling, which is not modelled here.
