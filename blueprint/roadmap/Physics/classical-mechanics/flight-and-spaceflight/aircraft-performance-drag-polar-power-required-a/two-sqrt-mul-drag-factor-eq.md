# Two sqrt mul drag Factor eq

Engineering form of the bound, an identity for all parameters:
`2 * √(a * b) = 2 * |W| * √(CD0 * k)`. For positive weight and `ρ, S, CD0, k > 0` it is the
minimum drag (`isLeast_levelDrag`); in level flight the lift equals the weight `W`, so the
greatest lift-to-drag ratio is `W / (2 * W * √(CD0 * k)) = 1 / (2 * √(CD0 * k))`. That
consequence needs `W > 0`: for `W < 0` the lift is negative and the ratio at minimum drag is
`-1 / (2 * √(CD0 * k))`.
