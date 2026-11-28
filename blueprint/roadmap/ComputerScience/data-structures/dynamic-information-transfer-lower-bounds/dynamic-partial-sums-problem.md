# Dynamic partial sums over a group

Let $(G, +)$ be a finite group whose elements are encoded in $\delta = \lceil \log_2 |G| \rceil$ bits. The *dynamic partial sums problem* over $G$ maintains an array $A[1..n] \in G^n$, initially all zero, under $\mathrm{update}(i, g)$, which sets $A[i] \leftarrow g$, and $\mathrm{sum}(i)$, which returns $A[1] + A[2] + \dots + A[i]$ (in this order when $G$ is non-abelian).

## Depends on

- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
- Michael L. Fredman, Michael E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", STOC (1989).
