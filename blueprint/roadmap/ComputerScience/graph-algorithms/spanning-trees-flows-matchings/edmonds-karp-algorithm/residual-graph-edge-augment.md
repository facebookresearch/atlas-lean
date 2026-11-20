# New residual arcs reverse the augmenting path (Edmonds–Karp, Proposition 2)

Let $c$ be natural-number capacities and $f$ an integer flow matrix (any integer matrix) on the vertices $0, \dots, n-1$, so that $(u, v)$ is a residual arc when $f(u, v) < c(u, v)$. Augment $f$ along a vertex list $p$ by an amount $\varepsilon \ge 0$. Then every residual arc of the new flow is a residual arc of $f$ or the reverse $(v, u)$ of a step $(u, v)$ of $p$.

This is Edmonds and Karp's Proposition 2: an arc can only enter the residual network if the augmentation pushed flow against it, which happens only on the reverses of path arcs. The statement needs no feasibility and no shortest-path assumption, and holds for any nonnegative amount, not only the bottleneck.

## Informally uses

- [Augmentation decreases a skew flow only against the path](edge-delta-nonneg-of-not-mem.md): the flow on $(u, v)$ can only drop when $(v, u)$ is a path step.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 2 and 3, Lemmas 1 and 2, Theorem 1).
