# Periodic Mask

`periodicMask m k = (2 ^ (m * k) - 1) / (2 ^ m - 1)`. For `0 < m` this is the sum of the
`2 ^ (m * j)` for `j < k`, so its binary digits equal to `1` are exactly those at the positions
`0, m, 2 * m, …, (k - 1) * m` (`testBit_periodicMask`).
