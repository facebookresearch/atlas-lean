# Affine-gap score from a gap state

For integer substitution scores $\sigma$, gap scores $o, e$, an [alignment](../pairwise-sequence-alignment/alignment.md) $A$ and a [gap state](gap-state.md) $p$, the score $V(A, p)$ is defined by

- $V(\text{empty}, p) = 0$;
- $V((a, b) A', p) = \sigma(a, b) + V(A', \varnothing)$;
- $V((a, -) A', p) = \gamma(p, X) + V(A', X)$ and $V((-, b) A', p) = \gamma(p, Y) + V(A', Y)$;
- $V((-, -) A', p) = V(A', \varnothing)$,

where $\gamma$ is the [gap cost](gap-cost.md).
