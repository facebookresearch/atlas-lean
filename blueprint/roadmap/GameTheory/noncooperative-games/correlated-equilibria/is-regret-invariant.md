# Regret-invariant mixed action

Let $\lambda(j, k)$ be real numbers indexed by pairs of strategies of a player (in the intended use,
its nonnegative regrets for switching from $j$ to $k$), and let $q$ be real weights on its strategies
(a mixed action in the intended use). Then $q$ is regret-invariant for $\lambda$ if the regret
flowing into each strategy equals the regret flowing out of it:

$$\sum_k q(k)\,\lambda(k, j) = q(j) \sum_k \lambda(j, k) \quad \text{for all } j .$$

When $\lambda \ge 0$ and $q$ is a probability vector, this says that $q$ is an invariant probability
vector of the stochastic matrix with off-diagonal entries $\lambda(j, k)/\mu$, for $\mu$ large. Foster and Vohra's calibrated forecasts use the
same conservation condition, their equation (2).

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §3, (3.1).
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §10.2, (12).
- D. P. Foster and R. V. Vohra, "Asymptotic calibration", Biometrika 85(2) (1998), 379–390, §5,
  equation (2).
