# Structural stability of invasion graphs for Lotka–Volterra systems

Consider $\dot u_i = u_i(b_i + \sum_j a_{ij} u_j)$ on $\mathbb R^n_{\ge 0}$ with a Volterra–Lyapunov stable interaction matrix $A$ (some positive diagonal $D$ makes $DA + A^{\mathsf T} D$ negative definite). For a growth-rate vector $b$, let $\mathcal E(A,b)$ be the admissible communities (supports of nonnegative equilibria) and $r_i^{A,b}(I) = b_i + \sum_{j \in I} a_{ij} u^*_j(I)$ the invasion rates. Call $(A,b)$ **hyperbolic** if $r_i^{A,b}(I) \ne 0$ for all $I \in \mathcal E(A,b)$ and $i \notin I$; the **invasion scheme** is the sign table $\operatorname{sgn} r_i(I)$.

1. **Robustness.** If $(\bar A, \bar b)$ is hyperbolic, there is $\varepsilon > 0$ such that for all $A$ within $\varepsilon$ of $\bar A$ and $b$ within $\varepsilon$ of $\bar b$: $A$ is Volterra–Lyapunov stable, $\mathcal E(A,b) = \mathcal E(\bar A,\bar b)$, and every invasion rate keeps its sign. Hence the invasion graphs, and therefore the graphs of heteroclinic connections between equilibria, of $(A,b)$ and $(\bar A,\bar b)$ coincide: the system is structurally stable within the Volterra–Lyapunov stable class.
2. **Maximal neighbourhood.** For fixed $A$ and hyperbolic $(A, \bar b)$ there is a unique maximal open set $N(\bar b) \ni \bar b$ of growth vectors with the same admissible communities, all equilibria hyperbolic and the same invasion graph.
3. **Conical partition.** $N(\bar b)$ is an open convex cone, and any hyperbolic $b$ with the same invasion scheme as $\bar b$ lies in $N(\bar b)$. Consequently the hyperbolic growth vectors split $\mathbb R^n$ into finitely many disjoint open convex cones, one per invasion scheme, each carrying a fixed assembly graph; crossing a cone boundary forces some invasion rate through zero (a non-hyperbolic equilibrium).

## Depends on

- [Invasion graph equals the graph of connections for Volterra–Lyapunov stable Lotka–Volterra systems](invasion-graph-equals-the-graph-of-connections-for-volterra-lyapunov-stable-lotka-volterra-systems.md)

## Expansion

Volterra–Lyapunov stability is an open condition, and for an admissible $I$ the equilibrium solves $A_{II} u^*_I = -b_I$ with $A_{II}$ invertible, so $u^*_I$ and the invasion rates depend continuously on $(A,b)$. Strict positivity of $u^*_I$ and strict signs of $r_i(I)$ persist under small perturbations, and no new community can become admissible nearby because that would require some $r_i(I)$ to vanish; this gives item 1, and by the coincidence of invasion graph and graph of connections the full connection structure is preserved. Item 2 takes the union of all neighbourhoods from item 1. For item 3, if two hyperbolic vectors $b^1, b^2$ share the invasion scheme, then along $b^\lambda = \lambda b^1 + (1 - \lambda) b^2$ the equilibria are $u^*_I(b^\lambda) = \lambda u^*_I(b^1) + (1-\lambda) u^*_I(b^2)$ (linearity) and each invasion rate is the same convex combination, so supports and signs are constant along the segment; scaling $b \mapsto \alpha b$ scales $u^*$ and all $r_i$ by $\alpha > 0$. Thus each scheme occupies a convex cone of growth vectors.

## Sources

- P. Almaraz, P. Kalita, J. A. Langa, F. Soler-Toscano, "Structural stability of invasion graphs for Lotka–Volterra systems", *Journal of Mathematical Biology* (2024), Section 5 (Theorems 28–29, Lemma 30, Theorem 32), <https://doi.org/10.1007/s00285-024-02087-8> (PMC11023985).
