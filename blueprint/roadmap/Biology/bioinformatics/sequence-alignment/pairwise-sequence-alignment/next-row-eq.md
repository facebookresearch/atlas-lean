# One row of the Needleman–Wunsch table

For every letter $a$ and sequences $p, y$, the [next row](next-row.md) for $a$ and $y$ of the row $\bigl(\mathrm{NW}(p, q)\bigr)_q$ is the row $\bigl(\mathrm{NW}(p a, q)\bigr)_q$, where $q$ runs over the prefixes of $y$, shortest first, and $\mathrm{NW}$ is the [Needleman–Wunsch score](nw-score.md).
