# Dixon's Q statistic

Dixon's Q statistic for observation `j` of the sample `x`: the gap to the nearest other
observation over the sample range, `nearestGap x j / sampleRange x`, and `0` when the range is
`0` (no spread, hence no rejection). Dixon's procedure applies it to an extreme observation of a
sample of at least three observations (`dixonReject` requires both); for two distinct observations
`Q = 1` whatever the data. Tabulated critical values, and any error-rate meaning of the
comparison, assume i.i.d. normal sampling, which is not modelled here.
