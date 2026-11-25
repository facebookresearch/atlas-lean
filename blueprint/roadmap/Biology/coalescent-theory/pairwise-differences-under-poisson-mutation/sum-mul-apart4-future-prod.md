# Remaining product moment $11/9$ from four distinct lineages

Let `a`, `b`, `c`, `d` be genes, `t ≤ n - 1`, and `Y` a real function on the [ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes
that [depends only on the first `t` steps](depends-before.md). Write `F_h` for the indicator that `a`, `b`, `c`, `d` are in
[four distinct lineages](apart4.md) after `t` events of `h`. Then

`∑_h Y(h) F_h P_h({a, b}, {c, d}, t) = (11/9) ∑_h Y(h) F_h`,

where the sums run over all histories and `P_h` is the
[conditional product moment of the remaining coalescence times](future-prod.md). Under [random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining.md)
every history has the [same probability](../ranked-labeled-histories-of-coalescent-trees/random-joining-singleton.md), so in the [Kingman genealogy](kingman-genealogy-measure.md) this says: given the first `t` steps
and that the four genes are still in four distinct lineages, the remaining coalescence times of
`{a, b}` and `{c, d}` after `t` events have product moment `11/9`. While the four are apart
with `m` lineages, the next event merges one of the four cross pairs with probability
`4/C(m, 2)` (leaving two pairs that share a lineage, with remaining product moment `4/3`), merges
`{a, b}` or `{c, d}` (ending one of the pairs) with probability `2/C(m, 2)`, and otherwise
keeps all four apart.
