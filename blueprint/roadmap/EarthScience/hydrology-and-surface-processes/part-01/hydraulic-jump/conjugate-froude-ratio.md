# Conjugate depth ratio from the upstream Froude number

Let `g > 0` be the gravitational acceleration, `q` a discharge per unit width, and `h1, h2 > 0`
depths in a rectangular channel satisfying the hydraulic-jump momentum identity
`q ^ 2 / g = h1 * h2 * (h1 + h2) / 2`. With the upstream squared Froude number
`Fr = q ^ 2 / (g * h1 ^ 3)`, the depth ratio is the positive root of `r * (1 + r) / 2 = Fr`:
`h2 / h1 = (√(1 + 8 * Fr) - 1) / 2`. Moreover the downstream depth is strictly larger exactly when
the upstream flow is supercritical: `h1 < h2` if and only if `Fr > 1`.
