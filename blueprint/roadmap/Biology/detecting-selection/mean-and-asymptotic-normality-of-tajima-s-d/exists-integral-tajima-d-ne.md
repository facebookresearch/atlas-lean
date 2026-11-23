# `E(D) ≠ E(N) / E(√V)`

A law of data for `n = 4` genes under which Tajima's numerator
`N = π - S / a₁` has mean `0` while `D = N / √V` has positive mean. The two outcomes are
realizable data sets: one doubleton site (`S = 1`, `π = 2 · 2 / 6 = 2/3`) with probability `3/7`,
and two singleton sites (`S = 2`, `π = 2 · 3 / 6 = 1`) with probability `4/7`. Here
`N = 4/33` and `N = -1/11` respectively, so `E[N] = 0`, but the negative value of `N` is divided
by the larger denominator. The law is not that of the neutral coalescent; the point is that
`E[N] = 0` (the conclusion of `KingmanTimes.integral_tajimaNumerator`) does not by itself force
`E[D] = 0`.
