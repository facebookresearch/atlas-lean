# Counting the pairs of lineages whose sorted labels avoid a set

Let `k` be a natural number and `S` a finite set of pairs `(p, q)` of natural numbers with
`p < q < k`. The number of [unordered pairs](../ranked-labeled-histories-of-coalescent-trees/lineage-pair.md) of the `k` lineages whose
[smaller](pair-lo.md) and [larger](pair-hi.md) labels `(p, q)` do not lie in `S` is
`C(k, 2) - #S`. The condition on `S` matters: an element of `S` not of this form is the sorted
label pair of no pair of lineages, and the count then exceeds `C(k, 2) - #S`.
