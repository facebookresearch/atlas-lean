# Ramp sum of a count

For a natural number `k` and a real `u`, the ramp sum is `R_k(u) = ∑_{h<k} max (u - h) 0`, a sum of
`k` ramps with kinks at `0, 1, …, k - 1`. In particular `R_0 = 0`, and `R_k(u) = 0` for every
`u ≤ 0`.

It is the twice-integrated unit masses at `0, 1, …, k - 1`: for every real `u`,
`R_k(u) = ∫₀ᵘ G_k(v) dv`, where `G_k(v)` is the number of the points `0, 1, …, k - 1` that are at
most `v` (the distribution function of these unit masses). `G_k` is the contribution of one count
`k` to the distribution function `G` of Levin and Reeds (1977).
