# Poisson–Gamma duality

Let $k \in \mathbb{N}$, $r > 0$ and $x \ge 0$. The gamma law $\Gamma(k + 1, r)$ with shape $k + 1$
and rate $r$ has upper tail

$$P\bigl(\Gamma(k + 1, r) > x\bigr) = F_k(rx) = \sum_{j=0}^{k} e^{-rx} \frac{(rx)^j}{j!},$$

where $F_k$ is the [Poisson distribution function](poisson-cdf.md): the probability that the
$(k+1)$-st point of a rate-$r$ Poisson process comes after time $x$ is the probability of at most
$k$ points in $[0, x]$.
