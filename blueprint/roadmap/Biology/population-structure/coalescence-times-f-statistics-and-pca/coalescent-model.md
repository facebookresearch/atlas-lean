# Coalescent model linking heterozygosity and coalescence times

The relation between allele frequencies and coalescence times under neutral
infinite-sites mutation, taken as the model assumption: the expected heterozygosity between
populations `X` and `Y` is `θ` times the expected coalescence time `coalTime X Y` of a gene
from `X` and a gene from `Y` (two genes drawn independently, so with replacement, when
`X = Y`). Time is in units of `2N` generations and `θ = 4Nu`. The measure `μ` is finite: it
ranges over the evolutionary randomness and, in practice, over a finite set of loci. For
`θ = 0` the coalescence times are not determined by the frequencies, and the identities below
then say that the f-statistics vanish.
