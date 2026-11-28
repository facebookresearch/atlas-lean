# Metric trees ($\mathbb{R}$-trees)

A metric space $(X, d)$ is a metric tree (an $\mathbb{R}$-tree) when

- it is geodesic: for all $x, y \in X$ there is $\gamma : \mathbb{R} \to X$ with $\gamma(0) = x$, $\gamma(d(x, y)) = y$ and $d(\gamma(s), \gamma(t)) = \lvert s - t \rvert$ for all $s, t \in [0, d(x, y)]$; and
- it is $0$-hyperbolic: for all $x, y, z, w \in X$,

    $$\min\bigl((x \mid y)_w,\ (y \mid z)_w\bigr) \le (x \mid z)_w,$$

    where $(x \mid y)_w = \tfrac12\bigl(d(x, w) + d(y, w) - d(x, y)\bigr)$ is the Gromov product.
