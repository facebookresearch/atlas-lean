# Dynamic prefix parity problem

The *dynamic prefix parity* problem maintains an array $A \in \mathbb{F}_2^n$, initially zero, under two operations: $\mathrm{update}(i, b)$ sets $A_i := b$, and $\mathrm{query}(i)$ returns $A_0 + A_1 + \dots + A_i \in \mathbb{F}_2$. It is the partial-sums problem over the group $\mathbb{Z}/2$.

## Depends on

- [State-transition specification of a data structure](../data-structure-interfaces-and-refinement/state-transition-specification.md)

## Sources

- M. L. Fredman and M. E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", Proceedings of the 21st ACM Symposium on Theory of Computing (STOC), pp. 345-354, 1989.
- M. Patrascu and E. D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4), pp. 932-963, 2006.
