# Curvature of the geotherm and slab profile and its heat equation

For a conductivity `k > 0` and all real `Ts`, `Tb`, `L` and `H`, the geotherm gradient
`d ↦ (Tb - Ts) / L + H * L / (2 * k) - H * d / k` has derivative `-H / k` at every depth `d`, and
`k * (-H / k) + H = 0`: the geotherm satisfies the steady heat equation `k * T'' + H = 0`. With the
convention `x / 0 = 0` the constant term `(Tb - Ts) / L` is `0` when `L = 0`, which does not change
the derivative; the intended domain is `L > 0`.

In terms of the
[slab gradient](../../../Physics/heat-and-mass-transport/steady-conduction-with-internal-heat-sources/slab-gradient.md)
with the same parameters: for `k > 0`, the slab gradient has derivative `-H / k` at every `d`, and
`k (-H / k) + H = 0`.
