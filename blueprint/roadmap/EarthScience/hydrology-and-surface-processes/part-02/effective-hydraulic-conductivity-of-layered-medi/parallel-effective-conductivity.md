# Effective conductivity for flow parallel to the layers

For `n` layers with thicknesses `L i` and conductivities `K i` (real numbers), the effective
conductivity for flow parallel to the layering is the thickness-weighted arithmetic mean
`K_par = (∑_{i<n} L i * K i) / (∑_{i<n} L i)`. It is defined for all real inputs, with the
convention `x / 0 = 0`: it is `0` when the total thickness `∑_{i<n} L i` is `0`, in particular for
`n = 0`. The intended domain is `n ≥ 1` with every `L i > 0` and `K i > 0`.
