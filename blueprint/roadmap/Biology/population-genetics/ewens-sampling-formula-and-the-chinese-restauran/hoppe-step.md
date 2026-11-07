# One step of Hoppe's urn

One step of **Hoppe's urn** on allelic partitions (Hoppe 1984): from a partition `π` of
`k`, the next gene carries a new allele with probability `θ / (θ + k)` (target parts
`1 ::ₘ π.parts`), and copies an allele carried by `j` genes with probability
`j * a j / (θ + k)`, where `a j = π.parts.count j` (target parts
`(j + 1) ::ₘ π.parts.erase j`). The value is the transition probability from `π` to `π'`.
