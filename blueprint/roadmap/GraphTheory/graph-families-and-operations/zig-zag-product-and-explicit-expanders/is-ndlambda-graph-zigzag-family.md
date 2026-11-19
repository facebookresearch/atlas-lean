# The zig-zag expander family consists of expanders

Let $K$ and $L$ be finite sets, $H$ a [rotation map](rotation-map.md) on $K \times L$ describing a $(\lvert K\rvert, \lvert L\rvert, 1/5)$-graph, and $e : (L \times L) \times (L \times L) \to K$ a bijection. Then for every $t$, the $t$-th graph $G_t$ of the [zig-zag family](zigzag-family.md) built from $H$ and $e$ is an $(\lvert K\rvert^{t+1}, \lvert L\rvert^2, 2/5)$-graph (O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Theorem 1.4, for a $(D^4, D, 1/5)$-graph $H$; the bijection $e$ exists exactly when $\lvert K\rvert = \lvert L\rvert^4$). The induction: $\lambda(G_t^2) \le (2/5)^2 = 4/25$, and the zig-zag theorem gives $4/25 + 1/5 + 1/25 = 2/5$.

For $D \ge 2$ a $(D^4, D, 1/5)$-graph needs a large degree $D$ (the degenerate seed $D = 1$, one vertex with one label fixed by the rotation map, is allowed and gives one-vertex graphs): the elementary lower bound $\lambda \ge \sqrt{(N - D)/(D(N - 1))}$, about $1/\sqrt D$ (the test-vector argument works for multigraphs as for simple graphs), forces $D \gtrsim 25$ for $\lambda \le 1/5$, and the Alon–Boppana bound $2\sqrt{D-1}/D$ is the asymptotic limit as $N$ grows with $D$ fixed; the paper obtains such a seed by exhaustive search or algebraic constructions (its Section 5). The theorem therefore reduces explicit constant-degree expanders of every size $D^{4i}$ to a single constant-size expander.

## Background

- [Zig-zag theorem](zig-zag-theorem.md): the step $\lambda(G^2 \circledcirc H) \le \lambda(G)^2 + \lambda(H) + \lambda(H)^2$.
- [Squaring squares the spectral parameter](is-ndlambda-graph-square.md): the squaring step.
- [Elementary lower bound on the spectral parameter](../expander-graphs/elementary-spectral-lower-bound.md):
  the finite bound that forces the seed to have large degree.
- [Alon-Boppana bound](../expander-graphs/alon-boppana.md): the asymptotic limit on $\lambda$ for fixed degree.
