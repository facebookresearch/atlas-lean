# Series flux through the effective conductivity

Let `n ≥ 1` layers, indexed in flow order `i = 0, …, n - 1`, have thicknesses `L i > 0` and
conductivities `K i > 0`, and let `head 0, …, head n` be the interface heads. If a common steady
Darcy flux `q` satisfies `head i - head (i + 1) = q * (L i / K i)` for every `i < n`, then
`q = K_eff * (head 0 - head n) / (∑_{i<n} L i)`, where
`K_eff = (∑_{i<n} L i) / (∑_{i<n} L i / K i)` is the effective conductivity in series.
