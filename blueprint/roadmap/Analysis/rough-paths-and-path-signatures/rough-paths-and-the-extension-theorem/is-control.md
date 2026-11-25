# Control function (Lyons)

A control on a set of times $J$ is a function $\omega(s, t)$ of $s \le t$ in $J$ that is
continuous, nonnegative, zero on the diagonal and superadditive:

$$\omega(s,t) + \omega(t,u) \le \omega(s,u) \qquad (s \le t \le u).$$

For a continuous path of finite $p$-variation, the $p$-th power of its $p$-variation over $[s, t]$ is the basic example; for a path in $\mathbb{R}^\iota$ ($\iota$ finite) with continuous velocity $v$, the $\ell^1$ length $\int_s^t \sum_j |v^j(u)|\,du$ is [another](is-control-length.md). Lyons calls $\omega$ regular when it is continuous near the diagonal and zero on it; continuity is required here on the whole set $\{(s, t) \in J^2 : s \le t\}$.

## Sources

- T. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14 (1998),
  Definition 1.2.2 and inequality (1.20).
