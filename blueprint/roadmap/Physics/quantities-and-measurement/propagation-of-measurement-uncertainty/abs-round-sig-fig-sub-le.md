# Rounding error is at most half a unit in the last place

Rounding to `k` significant figures, for a positive count `k : ℕ+`, changes `x` by at most
half a unit in the last reported place, `10 ^ (-sigFigShift k x)`.
