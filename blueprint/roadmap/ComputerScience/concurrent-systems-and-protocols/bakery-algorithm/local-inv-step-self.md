# A step of a process preserves its own bakery invariant

Let $s$ be a state of the bakery algorithm in which every process satisfies the [per-process invariant](local-inv.md). If process $i$ takes one [atomic action](local-step.md), then $i$ satisfies the invariant in the resulting state. The two informative cases are the loop statements. At L2, reading $\mathrm{choosing}[j] = 0$ means that $j$ is not in the doorway, so it is in its noncritical section (hence behind $i$) or holds a ticket and is no longer choosing. At L3, for $j \ne i$, passing $j$ while $j$ holds a ticket means that $(\mathrm{number}[j], j) \not< (\mathrm{number}[i], i)$, hence $(\mathrm{number}[i], i) < (\mathrm{number}[j], j)$ since the names differ; for $j = i$ no comparison is needed. This is the case analysis of Lamport's Assertion 2, carried out step by step.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: Assertion 2 and its proof, pp. 454–455.
