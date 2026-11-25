# One-generation transition matrix of the lineage count

For a [Cannings model](cannings-model.md) of a population of size `N` and a natural number `n`,
the one-generation transition matrix of the ancestral lineage count (block-counting process) on
the states `0, …, n` has entries `P_{b,a}`, the [transition probabilities](lineage-prob.md). Its
row `b` sums to `1` when `b ≤ N` ([row sums](../coalescent-limits-of-cannings-models/sum-lineage-prob.md));
a row with `b > N` is zero.
