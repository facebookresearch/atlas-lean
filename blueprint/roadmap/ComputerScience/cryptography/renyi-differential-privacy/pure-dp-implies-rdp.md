# Pure differential privacy implies Rényi differential privacy

Let $M$ be a discrete mechanism that is $(\varepsilon, 0)$-differentially private with respect to a symmetric adjacency relation, $\varepsilon \ge 0$. Then for every finite order $\alpha > 1$, $M$ is

$$
\Bigl(\alpha, \frac{\alpha\varepsilon^2}{2}\Bigr)\text{-Rényi differentially private},
$$

which matches $(\varepsilon^2/2)$-zero-concentrated differential privacy on all finite orders.

## Proof sketch

Symmetry gives the two-sided likelihood-ratio bound $e^{\pm\varepsilon}$ for every pair of adjacent datasets, and the moment bound then gives $D_\alpha(M(x) \Vert M(y)) \le \alpha\varepsilon^2/2$ for every finite $\alpha > 1$. The case $\varepsilon = 0$ is trivial.

## Depends on

- [Rényi divergence and Rényi differential privacy](renyi-differential-privacy.md)
- [Differential privacy](../differential-privacy/differentially-private.md)

## Proof depends on

- [Rényi-moment bound for bounded privacy loss](privacy-loss-moment-bound.md)
- [Differential privacy as a hockey-stick divergence bound](hockey-stick-characterization.md)

## Sources

- Mark Bun and Thomas Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", Theory of Cryptography (TCC 2016-B, Part I), 2016; arXiv:1605.02065v2, Proposition 3.3.
