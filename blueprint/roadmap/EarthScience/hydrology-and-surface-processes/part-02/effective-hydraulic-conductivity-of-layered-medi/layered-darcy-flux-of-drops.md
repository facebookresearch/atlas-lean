# Series flux from the per-layer head drops

Let `n ≥ 1` layers, indexed in flow order `i = 0, …, n - 1`, have thicknesses `L i > 0` and
conductivities `K i > 0`, and let `head 0, …, head n` be the interface heads. If a common steady
Darcy flux `q` satisfies the per-layer drop law `head i - head (i + 1) = q * (L i / K i)` for every
`i < n`, then `q` is the total head drop divided by the summed series resistance:
`q = (head 0 - head n) / (∑_{i<n} L i / K i)`. The per-layer drop law is a model assumption, not
derived.
