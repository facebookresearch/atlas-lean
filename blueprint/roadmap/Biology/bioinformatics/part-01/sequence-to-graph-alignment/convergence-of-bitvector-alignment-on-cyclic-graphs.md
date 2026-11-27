# Convergence of priority-ordered bit-vector alignment on cyclic graphs

Work with the sequence graph $G = (V, E, \sigma)$, query $s$ of length $m$ and the semi-global recurrence for $C_{i,j}$ of [Sequence-to-graph alignment recurrence and the vertical property](sequence-to-graph-alignment-recurrence-and-vertical-property.md), and store each node's column in bit-vector form. On graphs with cycles there is no topological order, so columns are recomputed until they stop changing:

- every column starts at $VP = 1^m$, $VN = 0^m$ (scores $1, 2, \dots, m$, the largest possible), and every node enters a priority queue with priority $0$;
- repeatedly pop a node $v$ of minimum priority; for each out-neighbour $y$, compute the column obtained from $v$'s column and the letter $\sigma(y)$ by one Myers step, and replace $y$'s column by the row-wise minimum of the old and new columns;
- if some row of $y$ decreased, push $y$ with priority equal to the **minimum changed score** $\min\{C^{\mathrm{new}}_{y,j} : C^{\mathrm{new}}_{y,j} < C^{\mathrm{old}}_{y,j}\}$ (lowering its priority if it is already queued).

Call a cell *converged* when its present score equals its correct score, the unique solution of the recurrence.

**Theorem (convergence order).** If the minimum priority in the queue is $x$, every cell whose correct score is below $x$ has converged.

**Corollary.** If all cells with correct score below $x$ have converged, then all cells with present score at most $x$ have converged.

**Theorem (pop bound).** No node is popped from the queue more than $m$ times.

Consequently, once the minimum priority reaches $m + 1$ all cells are correct; the outer loop runs at most $m|V|$ times and the edge relaxations at most $m\sum_v |\delta^{\mathrm{out}}_v| = m|E|$ times, so in the worst case the cyclic bit-vector algorithm does the work of a cell-by-cell algorithm. Since scores lie in $\{0, \dots, m\}$, the queue can be an array of $m + 1$ buckets with amortized constant-time operations.

## Depends on

- [Sequence-to-graph alignment recurrence and the vertical property](sequence-to-graph-alignment-recurrence-and-vertical-property.md)

## Expansion

*Convergence order*, by induction on $x$. Assume cells with correct score below $x - 1$ have converged and take a cell with correct score $x - 1$. If that score comes from the vertical term, its vertical neighbour has converged at $x - 2$, and the bit-vector encoding forces the cell's present score to be at most $x - 1$. If it comes from the horizontal term, or from a diagonal mismatch, the neighbouring column contained a converged cell of score $x - 2$, so that node was queued with priority at most $x - 2$ and the connecting edge was processed afterwards, writing the correct value. For a diagonal match the diagonal neighbour has the same correct score $x - 1$; following diagonal matches backwards must end, since diagonal steps decrease the row, at a cell covered by the previous cases, so the whole chain has converged.

*Corollary.* Present scores start at the maximum and recurrence updates never go below the correct score, so a present score $x$ with correct score below $x$ is excluded by hypothesis; hence present score $x$ is correct.

*Pop bound.* A pop of $v$ with priority $x$ means some cell of $v$ had present score $x$ when it was queued; by the convergence order and the corollary that cell had converged. So each pop is preceded by an update that made at least one new cell of $v$ converge, which can happen at most $m$ times per column.

## Sources

- M. Rautiainen, V. Mäkinen and T. Marschall, "Bit-parallel sequence-to-graph alignment", Bioinformatics 35(19) (2019), 3599–3607, Section 4.1 (minimum changed score), Section 4.3 (Algorithm 2, Theorem 2, Corollary 1, Theorem 3), <https://doi.org/10.1093/bioinformatics/btz162> (PMC6761980).
