# Effective conductivity of layers in series

For `n` layers indexed in flow order `i = 0, …, n - 1`, with thicknesses `L i` and hydraulic
conductivities `K i` (real numbers), the effective hydraulic conductivity of the layers in series
is the total thickness divided by the summed layer resistances `L i / K i`:
`K_eff = (∑_{i<n} L i) / (∑_{i<n} L i / K i)`. It is the series conductivity implied by a common
steady Darcy flux `q` through continuous interface heads with the per-layer drops
`head i - head (i + 1) = q * (L i / K i)`; Darcy's law itself is assumed, not derived.

It is defined for all real inputs, with the convention `x / 0 = 0`: a layer with `K i = 0`
contributes `0` to the summed resistance, as if it offered no resistance (an impermeable layer is
outside the domain of the formula), and `K_eff = 0` when the summed resistance is `0`, in
particular for `n = 0`. The intended domain is `n ≥ 1` with every `L i > 0` and `K i > 0`.
