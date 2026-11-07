# Sturm separation theorem

Let $p, q, y_1, y_2 : \mathbb{R} \to \mathbb{R}$ and $a < b$,
and let $J \subseteq \mathbb{R}$ be an open connected set (an open interval, possibly unbounded)
containing $[a, b]$. Suppose that $p$ and $q$ are continuous on $J$, and that $y_1$ and $y_2$
are twice differentiable at every point of $J$ and solve $y'' + p(x)\, y' + q(x)\, y = 0$ at
every $x \in J$. Suppose further that the Wronskian $y_1 y_2' - y_2 y_1'$ is nonzero at some
point of $J$. If $y_1(a) = y_1(b) = 0$ and $y_1(x) \ne 0$ for every $x \in (a, b)$, then $y_2$
has exactly one zero in the open interval $(a, b)$.

## Sources

- C. Sturm, Mémoire sur les équations différentielles linéaires du second ordre, 1836. Via leanprover/lean-eval@38361be, problem `sturm_separation`.
