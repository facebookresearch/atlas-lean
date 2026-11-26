# Hitting-time identity

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops and with connected [underlying graph](../oriented-incidence-matrices/underlying-graph.md), and let $w : E \to (0, \infty)$ be conductances, with [Laplacian](../graph-laplacians-and-cheeger-s-inequality/laplacian.md) $L$ and [weighted degree](../../part-02/conductance-and-cheeger-s-inequality/weighted-degree.md) $\pi$. Let $a, z \in V$, let $h$ solve the [first-step equations](is-hitting-time-solution.md) of the hitting times of $z$, and let $v$ be the potential of a unit current from $a$ to $z$ vanishing at $z$: $L v = \delta_a - \delta_z$ and $v(z) = 0$. Then

$$h(a) = \sum_{x \in V} \pi(x)\, v(x)$$

(R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Proposition 2.20, due to Tetali, with $Z = \{z\}$).

The source states the identity for a vertex set $Z$ and the expected hitting time of the walk; on a connected loopless multigraph the expected hitting times are the unique solution of the first-step equations. On the path $0 - 1 - 2$ with unit conductances, the solution for $z = 2$ has $h(0) = 4 = 1 \cdot 2 + 2 \cdot 1 + 1 \cdot 0$.
