# One row of the Smith–Waterman table

For every letter $a$ and sequences $p, y$, the [next row](next-row.md) for $a$ and $y$ of the row $\bigl(H(p, q)\bigr)_q$ is the row $\bigl(H(p a, q)\bigr)_q$, where $q$ runs over the prefixes of $y$, shortest first, and $H$ is the [terminal Smith–Waterman cell](../pairwise-sequence-alignment/sw-cell-score.md).
