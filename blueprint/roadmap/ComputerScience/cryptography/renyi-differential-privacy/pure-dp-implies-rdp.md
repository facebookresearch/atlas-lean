# Pure differential privacy implies Rényi differential privacy

Let $M$ be a discrete mechanism that is $(\varepsilon, 0)$-differentially private with respect to a symmetric adjacency relation, $\varepsilon \ge 0$. Then for every finite order $\alpha > 1$, $M$ is

$$
\Bigl(\alpha, \frac{\alpha\varepsilon^2}{2}\Bigr)\text{-Rényi differentially private},
$$

which matches $(\varepsilon^2/2)$-zero-concentrated differential privacy on all finite orders.

## Proof sketch

Symmetry gives the two-sided likelihood-ratio bound $e^{\pm\varepsilon}$. By the moment bound, $D_\alpha \le \varepsilon\tanh(\varepsilon/2) + (\alpha-1)\varepsilon^2/2 \le \varepsilon^2/2 + (\alpha-1)\varepsilon^2/2 = \alpha\varepsilon^2/2$, using $\tanh(x) \le x$.

## Depends on

- [Rényi divergence and Rényi differential privacy](renyi-differential-privacy.md)
- [Differential privacy](../differential-privacy/differentially-private.md)

## Proof depends on

- [Rényi-moment bound for bounded privacy loss](privacy-loss-moment-bound.md)
- [Differential privacy as a hockey-stick divergence bound](hockey-stick-characterization.md)

## Sources

- Mark Bun and Thomas Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", Theory of Cryptography (TCC 2016-B, Part I), 2016.
