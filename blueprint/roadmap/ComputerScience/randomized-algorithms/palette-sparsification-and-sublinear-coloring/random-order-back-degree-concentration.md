# Concentration of the number of later-processed neighbors under a random order

With $\pi$ as in the asymmetric list-size lemma, let $\deg^{<}_\pi(v)$ be the number of neighbors $u$ of $v$ with $\pi(u) < \pi(v)$. For all sufficiently large $n$ and every vertex $v$ with $\pi(v) > 40 n\ln n/(\deg(v) + 1)$ (a condition on the random value $\pi(v)$),

$$
\Pr\Big[\deg^{<}_\pi(v) < \frac{\deg(v)\,\pi(v)}{2n} \;\Big|\; \pi(v)\Big] \le n^{-2.4}.
$$

## Proof sketch

Condition on $\pi(v) = i + 1$. The neighbors of $v$ preceding $v$ form a uniformly random subset of the other $n - 1$ vertices restricted to the first $i$ positions, so $\deg^{<}_\pi(v)$ is hypergeometric with parameters $N = n - 1$, $K = i$, $M = \deg(v)$ and mean $\deg(v)\,i/(n-1)$. The target threshold is at most about half the mean, and the hypergeometric lower tail $\exp(-t^2/(2\mu))$ with $t \approx \mu/2$ gives $\exp(-(1 - o(1))\mu/8)$; the hypothesis on $\pi(v)$ makes $\mu \ge (1 - o(1))\, 40\ln n$, hence the bound $n^{-2.4}$ for large $n$.

## Depends on

- [List sizes inversely proportional to a random rank have average O(log^2 n)](asymmetric-list-sizes-from-random-ranks.md)

## Proof depends on

- [List sizes inversely proportional to a random rank have average O(log^2 n)](asymmetric-list-sizes-from-random-ranks.md)
- [Hypergeometric distribution](../../../Probability/distributions/discrete/hypergeometric-distribution/hypergeometric.md)

## Sources

- Sepehr Assadi, Helia Yazdanyar, "Simple Sublinear Algorithms for (Delta+1) Vertex Coloring via Asymmetric Palette Sparsification", SOSA (2025), arXiv:2502.17629.
