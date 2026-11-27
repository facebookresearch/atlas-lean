# Statistical distance of products and with shared public samples

Let $\delta$ denote statistical distance of distributions on finite sets.

1. (Products) $\delta(\bigotimes_{i} p_i, \bigotimes_i q_i) \le \sum_i \delta(p_i, q_i)$, so $\delta(\mu^{\otimes k}, \nu^{\otimes k}) \le k\,\delta(\mu,\nu)$; the same holds when the coordinates are only conditionally independent given a shared public sample that is revealed on both sides.
2. (Shared sample) If $s \sim \pi$ is revealed and $x \sim K(s)$ or $x \sim L(s)$, then $\delta\big((s, K(s)), (s, L(s))\big) = \mathbb{E}_{s\sim\pi}[\delta(K(s), L(s))]$ and its square is at most $\mathbb{E}_s[\delta(K(s), L(s))^2]$.
3. (Convexity) $\delta(\sum_a p(a) f(a), q) \le \sum_a p(a)\,\delta(f(a), q)$.
4. (Bounded scores) For $g$ with $|g| \le B$, $|\mathbb{E}_p g - \mathbb{E}_q g| \le 2B\,\delta(p,q)$, and $\sum_a \min(p(a), q(a)) = 1 - \delta(p,q)$.

## Proof sketch

For products, replace one coordinate at a time (hybrid argument) and use the triangle inequality; each step costs that coordinate's distance. The shared-sample identity holds because the joint laws agree on the first coordinate, so the $\ell_1$ distance splits over $s$. The remaining items are Jensen's inequality and direct computations with the positive part of $p - q$.

## Depends on

- [Total variation distance between finite measures](../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
- A. Sahai and S. Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2), 2003.
