# Central limit theorem and stickiness of Fréchet means on spiders

**Setting.** The space $T_3$ of phylogenetic trees with three leaves and one interior edge length is the **3-spider**: three half-lines (legs) glued at a common origin $C$, the star tree. More generally, a $p$-spider $S_p$ has legs $L_1,\dots,L_p$, each isometric to $[0,\infty)$, with the intrinsic (geodesic) metric. Distances between points on the same leg are differences, and distances between points on different legs pass through $C$. A probability measure $Q$ on $S_p$ decomposes as

$$Q(A) = w_0\,Q_0(A\cap C) + \sum_{k=1}^p w_k\,Q_k(A\cap L_k),$$

where $Q_k$ is a probability on $L_k$ with mean $\nu_k = \int u\,Q_k(du) > 0$. Let $X_1, X_2,\dots$ be i.i.d. with law $Q$ and finite second moment. Let $\mu_I$ be the intrinsic (Fréchet) mean, the minimizer of $x\mapsto\mathbb{E}\,d(x,X_1)^2$, and $\bar X_{n}$ the sample Fréchet mean. Both exist and are unique because $S_p$ is a CAT(0) space.

**Theorem.** Assume $w_0 = 0$ and write $v_k = w_k\nu_k$.

For a leg $a$, the **fold onto $L_a$** is the map $\phi_a: S_p\to\mathbb{R}$ sending a point of $L_a$ at distance $u$ from $C$ to $u$, and a point of any other leg at distance $u$ to $-u$; let $Y_i = \phi_a(X_i)$, so that $\mathbb{E}\,Y_1 = v_a - \sum_{b\ne a}v_b$.

1. If $v_a > \sum_{b\ne a}v_b$ for some leg $a$, then $\mu_I \in L_a$ at distance $v_a - \sum_{b\ne a}v_b$ from $C$. Almost surely $\bar X_n\in L_a$ for all sufficiently large $n$, and $\sqrt n\,(\phi_a(\bar X_n) - \phi_a(\mu_I))$ converges in distribution to $N(0,\sigma_a^2)$ with $\sigma_a^2 = \operatorname{Var} Y_1$.
2. If $v_a = \sum_{b\ne a}v_b$ for some leg $a$ and every other leg is strictly subcritical, $v_b < \sum_{c\ne b}v_c$ for all $b\ne a$ (so $a$ is the unique **critical** leg; this extra condition fails only when exactly two legs carry mass, where $S_p$ reduces to a line and the ordinary CLT applies), then $\mu_I = C$. Almost surely $\bar X_n \in L_a\cup\{C\}$ for all sufficiently large $n$, and $\sqrt n\,\phi_a(\bar X_n)$ converges in distribution to $\max(Z,0)$, the **positive part** of $Z\sim N(0,\sigma_a^2)$ with $\sigma_a^2 = \mathbb{E}\,Y_1^2 > 0$. The limit has an atom of mass $1/2$ at $0$: with asymptotic probability $1/2$ the sample mean sits exactly at $C$ (partial stickiness). The limit is the projection of the Gaussian onto $[0,\infty)$, not its reflection $|Z|$.
3. If $v_a < \sum_{b\ne a}v_b$ for every $a$, then $\mu_I = C$, and almost surely there is a finite random sample size $N$, depending on the sample path, such that $\bar X_n = C$ for all $n\ge N$.

In case 3 the sample mean is **sticky**: almost surely it equals the star tree exactly for all large samples, so the usual $\sqrt n$ fluctuations vanish. No fixed sample size guarantees this; $N$ is random. Stickiness can be checked directly from leg weights and leg means, without fitting any model.

## Expansion

For $x$ at distance $x$ from $C$ on leg $L_a$, the Fréchet function is

$$F(x) = x^2 + 2\Big(\sum_{b\ne a}v_b - v_a\Big)x + \text{const},$$

because points on other legs are at distance $x+u$ and points on $L_a$ at distance $|x-u|$. On each leg $F$ is a quadratic with vertex at $v_a - \sum_{b\ne a}v_b$. If the vertex is positive on some leg, the minimum lies inside that leg. Otherwise every leg's quadratic increases away from $C$, so the minimizer is $C$. The sample version replaces $v_k$ by empirical leg averages, so $\bar X_n$ lies on $L_a$ at distance $\bar Y_n = \frac1n\sum_{i\le n} Y_i$ when $\bar Y_n>0$ and at $C$ when $\bar Y_n\le0$ and no other leg has an empirical majority. Under strict inequalities, the strong law of large numbers makes the sample signs agree with the population signs for all large $n$ (a random, almost surely finite threshold), which gives stickiness in case 3 and a Euclidean CLT for $\bar Y_n$ in case 1. In case 2 the other legs are strictly subcritical, so eventually none of them carries the sample mean, and $\sqrt n\,\phi_a(\bar X_n) = \sqrt n\,\max(\bar Y_n,0)$, whose limit is $\max(Z,0)$ by the classical CLT for $\bar Y_n$ and the continuous mapping theorem. For example, with unit-length observations on three legs chosen with probabilities $1/2,1/4,1/4$, leg $1$ is critical and the sample mean is exactly $C$ whenever leg $1$ holds fewer than half of the observations, an event of asymptotic probability $1/2$. For four-leaf trees the space $T_4$ consists of $15$ quadrants glued along shared axes, and the source encodes such data through the associated Petersen graph. The source uses these results to compare samples of SARS-CoV-2 genome trees.

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)
- [Lindeberg–Feller central limit theorem](../../../../Probability/central-limit-theorems/lindeberg-feller-central-limit-theorem/lindeberg-feller-clt-triangular.md)
- [Continuous mapping theorem for weak convergence of probability measures](../../../../Probability/convergence-of-measures/continuous-mapping-theorem/tendsto-map-of-tendsto-of-ae-continuous.md)

## Sources

- C. Shen, V. Patrangenaru and R. Moore, "A Phylogenetic Trees Analysis of SARS-CoV-2", arXiv:2106.06918 (2021), Section 3, Theorem 2 and Corollary 3, <https://doi.org/10.48550/arXiv.2106.06918>.
- T. Hotz, S. Huckemann, H. Le, J. S. Marron, J. C. Mattingly, E. Miller, J. Nolen, M. Owen, V. Patrangenaru and S. Skwerer, "Sticky central limit theorems on open books", Ann. Appl. Probab. 23 (2013), 2238–2258, Proposition 5.6 and the partly sticky central limit theorem (a $p$-spider is an open book with a one-point spine), <https://doi.org/10.1214/12-AAP899>.
