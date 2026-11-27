# Preflows, valid labelings, push and relabel

A **preflow** in a network $N$ is an integral arc function $f$ with $0 \le f \le$ capacity such that the **excess** $e(v) = \text{inflow}(v) - \text{outflow}(v)$ is nonnegative at every vertex $v \ne s$. A **valid labeling** is a function $h : V \to \mathbb{N}$ with $h(s) = |V|$, $h(t) = 0$ and $h(u) \le h(v) + 1$ for every residual arc $u \to v$. A vertex $v \notin \{s, t\}$ is **active** if $e(v) > 0$. **Push**$(u, v)$ applies to an active $u$ and a residual arc $u \to v$ with $h(u) = h(v) + 1$ and moves $\min(e(u), \text{res}(u, v))$ units; it is **saturating** if it uses all residual capacity. **Relabel**$(u)$ applies to an active $u$ with no admissible arc and sets $h(u)$ to $1 + \min\{h(v) : u \to v \text{ residual}\}$.

## Depends on

- [Feasible flow](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/is-feasible-flow.md)

## Sources

- A. V. Goldberg and R. E. Tarjan, "A New Approach to the Maximum-Flow Problem", Journal of the ACM 35(4), 1988.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
