# Garwood's exact upper confidence bound

For a level $\alpha \in \mathbb{R}$ and an observed count $k \in \mathbb{N}$, Garwood's upper
confidence bound for a Poisson mean is

$$u_\alpha(k) = \sup\{ x \ge 0 : \alpha \le F_k(x) \},$$

where $F_k$ is the [Poisson distribution function](../poisson-gamma-duality-identity/poisson-cdf.md) and the supremum of an empty or
unbounded set is read as $0$ (this happens only for $\alpha > 1$ or $\alpha \le 0$). For
$0 < \alpha < 1$ it is the root of $F_k(u) = \alpha$ ([statement](poisson-cdf-garwood-upper.md)).

## Sources

- F. Garwood, *Fiducial limits for the Poisson distribution*, Biometrika 28 (1936), 437–442.
