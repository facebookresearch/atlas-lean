# For a radiosity solution, gray net power is emission minus absorption

Let `ι` be a finite set of surfaces with areas `A` and view factors `F` forming a
[black enclosure](is-black-enclosure.md), and let `J` solve the
[radiosity equations](is-radiosity.md) for `σ`, emissivities `ε` and temperatures `T`. Then for
every surface `i`, the [gray net power](gray-net-power.md) is
`q_i = A_i ε_i (σ T_i⁴ - ∑_j F_{ij} J_j)`: the emitted power minus the absorbed fraction `ε_i` of
the irradiation.
