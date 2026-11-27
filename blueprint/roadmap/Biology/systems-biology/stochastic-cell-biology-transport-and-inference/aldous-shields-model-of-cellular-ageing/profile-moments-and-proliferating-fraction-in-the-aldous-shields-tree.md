# Profile moments and proliferating fraction in the Aldous–Shields ageing tree

**Model.** Start with a single external vertex (the root, depth $0$) of the infinite binary tree. Each external vertex $u$ at depth $|u| = i$ splits at rate $c^{-i}$, becoming internal and creating two external children at depth $i+1$. Let $X_i(t)$ be the number of external vertices at depth $i$ at time $t$ (the profile). Fix $c > 1$ and set, for $k \ge 0$,

$$a_k = (-1)^k\frac{c^k}{(c-1)(c^2-1)\cdots(c^k-1)}, \qquad b_k = \frac{c^1c^2\cdots c^k}{(c-1)(c^2-1)\cdots(c^k-1)}, \qquad b_\infty = \prod_{l\ge1}(1 - c^{-l})^{-1},$$

with $a_0 = b_0 = 1$ and $a_k = b_k = 0$ for $k < 0$.

**Theorem (profile moments).** For $t > 0$ and $i > -n$,

$$\mathbb E\big[X_{n+i}(tc^n)\big] = 2^{n+i}\sum_{k=0}^n a_k b_{n-k}\, e^{-c^{-i+k}t} \;\approx\; b_\infty\, 2^{n+i}\sum_{k=0}^\infty a_k\, e^{-c^{-i+k}t} \quad (n \to \infty).$$

The covariances $\operatorname{Cov}[X_{n+i}(tc^n), X_{n+i'}(tc^n)]$, $i \le i'$, grow like $(2/c)^{2n}$ when $c < \sqrt2$, like $n\,2^n$ when $c = \sqrt2$, and like $2^n$ when $c > \sqrt2$, with explicit constants. Since all three rates are $o(4^n)$, the normalized profile $2^{-n}X_{n+i}(tc^n)$ concentrates around its mean for every $c > 1$.

**Cellular ageing.** Fix a maximal depth $h$ and a time scale $r > 0$; vertices at depth $h+1$ are senescent and never split, and a vertex at depth $|u| \le h$ splits at rate $r c^{-|u|}$. Let $Z^p(t)$ and $Z^s(t)$ count proliferating (depth $\le h$) and senescent (depth $h+1$) external vertices, and $L(t) = Z^p(t)/(Z^p(t) + Z^s(t))$.

**Theorem (frequency of replicating cells).** For every $t > 0$, in probability,

$$\lim_{h\to\infty} L(tc^h) = \frac{\sum_{i\ge0}\sum_{k\ge0} 2^{-i}a_k\, e^{-c^{i+k}t/r}}{\sum_{i\ge0}\sum_{k\ge0} a_k\big(2^{-i}e^{-c^{i+k}t/r} + 2\,e^{-c^{-i-1+k}t/r}\big)}.$$

## Expansion

The expected profile satisfies the linear system $\frac{d}{dt}\mathbb E X_i = 2c^{-(i-1)}\mathbb E X_{i-1} - c^{-i}\mathbb E X_i$, which is triangular and solved by sums of exponentials $e^{-c^{-j}t}$; the coefficients are $q$-binomial-type products in $q = 1/c$, and $b_\infty$, $\sum_k a_k e^{-c^k s}$ are the resulting $q$-series. Second moments obey a similar closed system for pairs of depths; the three covariance regimes come from comparing the growth $2^n$ of the number of vertices with $(2/c)^{2n}$ from correlations inherited along shared ancestry. For the ageing tree, below depth $h+1$ the process coincides with the Aldous–Shields tree, so $Z^p$ and $Z^s$ at time $tc^h$ are sums of profile values whose means are given by the first theorem; the concentration of these sums yields the ratio of means.

## Sources

- Katharina Best, Peter Pfaffelhuber, "The Aldous-Shields model revisited with application to cellular ageing", Electronic Communications in Probability 15 (2010), 475–488, <https://doi.org/10.1214/ecp.v15-1581>. Published version of arXiv:1004.1581, cited next; locators there refer to the arXiv version.
- Katharina Best, Peter Pfaffelhuber, "The Aldous-Shields model revisited (with application to cellular ageing)", arXiv (2010). Theorem 1, Definitions of the ageing process and of $L$, Theorem 2. <https://doi.org/10.48550/arXiv.1004.1581>
