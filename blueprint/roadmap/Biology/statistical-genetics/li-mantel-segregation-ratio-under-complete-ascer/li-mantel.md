# Li Mantel

The **Li–Mantel estimator** `(R - J) / (T - J)` of the segregation ratio from the first `n`
ascertained sibships of size `s`, where `T = n s` is the number of children. Since `J ≤ n`, the
denominator satisfies `T - J ≥ n (s - 1) > 0` whenever `n ≥ 1` and `s ≥ 2`, the intended domain.
Otherwise it can vanish (for `n = 0`, or for `s = 1`, where every sibship is a singleton), and
then the value is `0` because Lean's division is total (`x / 0 = 0`).
