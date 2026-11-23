# Max-product pruning recursion

Let $R$ be a linearly ordered commutative semiring, $S$ a finite nonempty state set and $\mathrm{obs}$ leaf weights. The max-product recursion on a [tree](../felsenstein-s-pruning-algorithm/tree.md) is

- for a leaf $l$: $M(l, s) = \mathrm{obs}(l, s)$;
- for an internal node with weights $P, Q$ and children $l, r$:

$$M(t, s) = \Bigl(\max_{a} P(s, a)\, M(l, a)\Bigr) \Bigl(\max_{b} Q(s, b)\, M(r, b)\Bigr).$$

When the leaf weights and all transition weights are nonnegative, $M(t, s)$ is the [maximal weight of a labeling](max-prune-eq-sup.md) given the root state $s$; for signed weights it is only the value of this recursion, attained by the [traceback](weight-traceback.md), and need not be maximal.
