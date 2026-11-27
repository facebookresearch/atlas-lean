# The mean minimizes the expected squared loss

Let $\nu$ be a probability measure on
$\mathbb{R}$ with mean $m = \int t \, d\nu(t)$ (taken to be $0$ when $\nu$ has no finite first
moment). Then for every $y \in \mathbb{R}$,

$$\int (\theta - m)^2 \, d\nu(\theta) \le \int (\theta - y)^2 \, d\nu(\theta),$$

where both integrals are taken in $[0, \infty]$.

When the right side is infinite the inequality is trivial; otherwise $\nu$ has a second moment and
the variance decomposition applies.
