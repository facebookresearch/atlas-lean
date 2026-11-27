# Uniform approximation by the smoothed function

Let $Q \subseteq F$ be compact and nonempty, $\varphi$ and $d$ continuous on $Q$ with $d \ge 0$ on $Q$, $\mu \ge 0$, and $D = \sup_{u \in Q} d(u)$. Then for every $x \in E$,

$$
f_\mu(x) \le f_0(x) \le f_\mu(x) + \mu D,
$$

where $f_\mu$ is the [smoothed max-type function](smoothed-max.md). The source assumes in addition that $Q$ and $\varphi$ are convex and $d$ strongly convex with $\min_Q d = 0$; the inequality needs only $d \ge 0$, so the statement above has weaker hypotheses. Combined with the Lipschitz bound $\|A\|^2/(\mu\sigma)$ on $\nabla f_\mu$ and an optimal method for smooth functions, the choice $\mu \sim \varepsilon/D$ gives an $\varepsilon$-solution of $\min f_0$ in $O(1/\varepsilon)$ iterations instead of the $O(1/\varepsilon^2)$ of subgradient methods (Theorem 3 of the source).

## Background

- [Nesterov's smoothed max-type function](smoothed-max.md): the definition, as a supremum over a compact set.

## Sources

- Yu. Nesterov, *Smooth minimization of non-smooth functions*, Math. Program. 103 (2005) 127–152, inequality (2.7).
