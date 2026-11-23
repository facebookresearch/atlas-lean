# Killing Coalescent

The **coalescent with killing** of a sample of `n` genes under infinite-alleles mutation,
through its competing clocks (time in units of `2N` generations, `θ = 4Nu`, mutations at rate
`θ / 2` per lineage, as in `KingmanTimes`). While the genealogy has `k` lineages
(`2 ≤ k ≤ n`), the next coalescence comes after time `C k ~ Exp(k.choose 2)` and the next
mutation after time `M k ~ Exp(k θ / 2)`, independently. Whichever comes first reduces the
number of lineages to `k - 1`: a coalescence merges two lineages, and a mutation founds an
allele carried by exactly the genes descending from that lineage, which is then removed
("killed") because earlier mutations on it are invisible in the sample. By memorylessness the
clocks restart at each level, so one independent pair of clocks per level determines the
sequence of events. The values of `C k`, `M k` for `k ∉ [2, n]` are irrelevant.
