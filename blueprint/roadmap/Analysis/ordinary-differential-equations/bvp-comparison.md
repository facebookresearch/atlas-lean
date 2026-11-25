# Comparison principle for the Dirichlet problem on $(0, 1)$

Let $J \subseteq \mathbb{R}$
be an open set containing $[0, 1]$, and let $u, v : \mathbb{R} \to \mathbb{R}$ be functions
that are differentiable at every point of $J$ and whose derivatives $u'$ and $v'$ are
differentiable at every point of $J$. If $-u''(x) \le -v''(x)$ for every $x \in (0, 1)$,
$u(0) \le v(0)$ and $u(1) \le v(1)$, then $u(x) \le v(x)$ for every $x \in [0, 1]$.

## Sources

- Standard maximum-principle argument; Protter-Weinberger. Problem `bvp_comparison` of the lean-eval benchmark.
