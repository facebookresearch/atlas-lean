# Log Strain

The logarithmic helper `ln(1 + e)`, for every real `e`. Lean totalizes `Real.log`, so it
also assigns values outside the physical domain, e.g. `logStrain (-1) = Real.log 0 = 0`; the
physical true strain is `trueStrain`, which requires `-1 < e`.
