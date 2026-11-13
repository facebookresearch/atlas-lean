# Probability of no recombination on a pair's genealogy

The probability that no recombination falls on the genealogy of a pair of lineages within
genetic distance `d` of the core, given that the pair coalesces at time `t` (time in units of
`2N` generations, `ρ = 4Nr` the scaled recombination rate per site): the two lineages carry
recombination events at total rate `ρ * d` until they coalesce.

In a mutation-free model this is a lower bound for the probability that the two haplotypes
are identical over the window — no recombination then implies identical windows, while a
recombined lineage may still carry the same alleles — so it is a lower bound for the
expected EHH, not its value. Without the mutation-free assumption the bound is not
established: mutations on either descendant branch can make the haplotypes differ even
with no recombination.
