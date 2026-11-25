# Lovász's bound on the Shannon capacity

Let $G$ be a simple graph on a finite set $V$ and, for each $k \ge 0$, let $H_k$ be a simple graph on the words $V^{k+1}$ such that any two distinct words $x, y$ that are not adjacent in $H_k$ have a coordinate $i$ with $x_i \ne y_i$ and $x_i, y_i$ not adjacent in $G$ (as in [Feasible values multiply along strong powers](pow-mem-theta-feasible.md)). If $\alpha(H_k)^{1/(k+1)} \to \theta$, then $\theta \le \vartheta(G)$. Taking $H_k = G^{\boxtimes (k+1)}$, the [strong powers](strong-power.md), $\theta$ is the [Shannon capacity](has-shannon-capacity.md) $\Theta(G)$ and this is Lovász's theorem

$$
\Theta(G) \le \vartheta(G).
$$

Every term of the sequence is at most $\vartheta(G)$ by [the bound on strong powers](indep-num-le-lovasz-theta-pow.md), so the limit is too.

## Background

- [Lovász's theorem: the Shannon capacity of the pentagon](shannon-capacity-pentagon.md): with $\vartheta(C_5) = \sqrt 5$ and $\alpha(C_5^{\boxtimes 2}) = 5$, this bound gives $\Theta(C_5) = \sqrt 5$.
- [Lovász's upper bound for the capacity of the 7-cycle](lovasz1979-upper-bound.md): the bound $\Theta(C_7) \le \vartheta(C_7)$ with Lovász's closed form for $\vartheta(C_7)$.

## Sources

- L. Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inform. Theory 25 (1979), 1–7.
- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, §20.
