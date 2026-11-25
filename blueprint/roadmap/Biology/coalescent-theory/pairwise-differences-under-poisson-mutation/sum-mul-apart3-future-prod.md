# Remaining product moment $4/3$ from three distinct lineages

Let `a`, `b`, `c` be genes, `t ≤ n - 1`, and `Y` a real function on the [ranked labeled histories](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes that
[depends only on the first `t` steps](depends-before.md). Write `T_h` for the indicator that `a`, `b`, `c` are in
[three distinct lineages](apart3.md) after `t` events of `h`. Then

`∑_h Y(h) T_h P_h({a, b}, {a, c}, t) = (4/3) ∑_h Y(h) T_h`,

where the sums run over all histories and `P_h` is the
[conditional product moment of the remaining coalescence times](future-prod.md). Under [random joining](../ranked-labeled-histories-of-coalescent-trees/random-joining.md)
every history has the [same probability](../ranked-labeled-histories-of-coalescent-trees/random-joining-singleton.md), so in the [Kingman genealogy](kingman-genealogy-measure.md) this says: given the first `t` steps
and that `a`, `b`, `c` are still in three distinct lineages, the remaining coalescence times of
`{a, b}` and `{a, c}` after `t` events have product moment `4/3`. While the three are apart
with `k` lineages, the next event merges `b` with `c` (leaving one pair, whose remaining time has
second moment `2`) with probability `1/C(k, 2)`, merges `a` with `b` or with `c` (ending one of
the pairs) with probability `2/C(k, 2)`, and otherwise keeps all three apart.
