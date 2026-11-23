# Effective conductivity for flow across the layers

For `n` layers with thicknesses `L i` and conductivities `K i` (real numbers), the effective
conductivity for flow in series across the layering is the total thickness over the summed layer
resistances, `K_ser = (∑_{i<n} L i) / (∑_{i<n} L i / K i)`. It is defined for all real inputs,
with the convention `x / 0 = 0`: a layer with `K i = 0` contributes `0` to the summed resistance,
and `K_ser = 0` when the summed resistance is `0`, in particular for `n = 0`. The intended domain is
`n ≥ 1` with every `L i > 0` and `K i > 0`. This is the same formula as the
[effective conductivity of layers in series](layered-effective-conductivity.md).
