# Number of alleles in the coalescent with killing

In a [coalescent with killing](killing-coalescent.md) of a sample of `n` genes with clocks `C k`
and `M k`, the number of alleles of the sample at an outcome `ω` is `K_n(ω) = 0` for `n = 0` and
otherwise `K_n(ω) = 1 + #{k : 2 ≤ k ≤ n, M k ω < C k ω}`: one allele for each level at which the
mutation clock rings strictly before the coalescence clock (a killing), plus one for the allele of
the last remaining lineage. The empty sample has no alleles, as the empty partition has no parts.
