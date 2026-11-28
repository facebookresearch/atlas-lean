# Diffusion approximation error for the neutral multi-allele Wright–Fisher model with mutation

**Model.** A diploid population of $N$ individuals carries $r \ge 2$ alleles $A_1,\dots,A_r$ at one locus. The Wright–Fisher chain $Y(n) = (Y_1(n),\dots,Y_{r-1}(n))$ of allele frequencies (with $Y_r = 1 - \sum_{i<r} Y_i$) has transitions

$$Y(n+1) \sim (2N)^{-1}\,\mathrm{Multinomial}\big(2N, (y_1^{\#},\dots,y_{r-1}^{\#})\big), \qquad y_i^{\#} = y_i\Big(1 - \sum_{j=1}^r u_{ij}\Big) + \sum_{j=1}^r u_{ji}y_j,$$

where $u_{ij} \in [0,1]$ is the probability that allele $A_i$ mutates to $A_j$. Assume genes mutate independently, $u_{ii} = 0$, and $u_{ki} = u_{ri}$ for all $k \neq i$ ($i \le r-1$). The approximating diffusion $X(t)$ on the simplex $I = \{x \in [0,1]^{r-1} : \sum x_i \le 1\}$ has generator

$$\mathcal{L} = \frac{1}{4N}\sum_{i,j=1}^{r-1} x_i(\delta_{ij} - x_j)\,\partial_{ij} + \sum_{i=1}^{r-1}\Big(-x_i\sum_{j=1}^r u_{ij} + \sum_{j=1}^r x_j u_{ji}\Big)\partial_i,$$

and its martingale problem is well posed from every starting point (strongly well posed when $r = 2$).

**Theorem.** For $r \ge 3$, every $n \in \mathbb{N}$, $f \in C_b^4(I)$ and $x \in I_{2N} = I \cap (2N)^{-1}\mathbb{Z}^{r-1}$,

$$\big|\mathbb{E}_x f(X(n)) - \mathbb{E}_x f(Y(n))\big| \le \sum_{m=1}^4 C_m\,\frac{1 - e^{-n\lambda_m^{\min}}}{1 - e^{-\lambda_m^{\min}}}\,\sup_{x \in I}\|\nabla^m f(x)\|_2,$$

where, for $m = 1,2,3,4$ and indices $1 \le k_1,\dots,k_m \le r-1$,

$$\lambda_{k_1,\dots,k_m} = \sum_{j=1}^r\sum_{i=1}^m u_{k_ij} + \sum_{i=1}^m u_{rk_i} + \frac{m(m-1)}{4N}, \qquad \lambda_m^{\min} = \min_{1 \le k_1,\dots,k_m \le r-1}\lambda_{k_1,\dots,k_m} .$$

Thus $\lambda_m^{\min} \ge m(m-1)/(4N) > 0$ for $m \ge 2$, while $\lambda_1^{\min} \ge 0$ vanishes when some allele $A_k$, $k \le r-1$, has $\sum_j u_{kj} + u_{rk} = 0$; when $\lambda_m^{\min} = 0$ the ratio is read as its limit $n$ (the geometric sum $\sum_{j=0}^{n-1}e^{-j\lambda}$ from which it arises). The constants are

$$C_1 = \tfrac12 b^\ast u^\ast, \qquad C_2 = \frac{\sqrt{r-2}}{8N\sqrt{r-1}}\Big(2u^\ast + \frac{1}{2N}\Big) + \frac{b^\ast}{2}\Big(b^\ast + \frac{\sqrt5}{4N}\Big) + \frac{(r-1)u^\ast}{\sqrt2}\Big(\frac1N + u^\ast\Big),$$

$$C_3 = \frac{\sqrt{r-2}}{8N\sqrt{r-1}}\Big(b^\ast + \frac{b^\ast}{\sqrt{r-1}} + \frac{3\sqrt2}{4N}\Big) + \frac16(r-1)^{3/2}\Big[\frac{1}{32N^2} + \frac{3u^\ast}{8N} + (u^\ast)^3\Big], \qquad C_4 = \frac{r-2}{32N^2(r-1)^{3/2}},$$

with

$$u^\ast = \max_{1 \le k \le r-1}\Big(\sum_{j=1}^r u_{kj} + u_{rk}\Big), \qquad b^\ast = \Big[\Big(\sum_{j=1}^r u_{i^\ast j}\Big)^2 + \sum_{i \ne i^\ast} u_{ri}^2\Big]^{1/2}, \qquad i^\ast \in \arg\max_i\Big(\sum_{j=1}^r u_{ij} + u_{ri}\Big).$$

So the $C_m$ are explicit polynomials in $u^\ast$, $b^\ast$ and $1/N$ (with $r$-dependent coefficients). For $r = 2$ the bound is fully explicit: with $u_{12}, u_{21}$ the two mutation probabilities, $\tilde\lambda_m = \frac{m(m-1)}{4N} + m(u_{12} + u_{21})$ and $\bar u = \max\{u_{12}, u_{21}\}$,

$$\big|\mathbb{E}_x f(X(n)) - \mathbb{E}_x f(Y(n))\big| \le \sum_{m=1}^4 \tilde C_m\,\frac{1 - e^{-n\tilde\lambda_m}}{1 - e^{-\tilde\lambda_m}}\,\sup_{x \in [0,1]}|f^{(m)}(x)|,$$

$$\tilde C_1 = \bar u\,(u_{12} + u_{21}), \quad \tilde C_2 = \frac{1}{64N^2} + \frac{u_{12} + u_{21}}{16N} + \bar u^{\,2} + \frac{5\bar u}{8N}, \quad \tilde C_3 = \frac{1}{48N^2} + \frac{\bar u}{8N} + \frac{\bar u^{\,3}}{6}, \quad \tilde C_4 = \frac{1}{512N^2}.$$

Here too $\tilde\lambda_1 = u_{12} + u_{21}$ may vanish, with the ratio then read as $n$. Since $\frac{1 - e^{-n\lambda}}{1 - e^{-\lambda}} \le \min\{n, (1 - e^{-\lambda})^{-1}\}$, the error is uniform in time when all the rates $\lambda_m^{\min}$ (resp. $\tilde\lambda_m$) are positive, and for $r = 2$ it is then of order $\bar u + 1/N$, needing only four derivatives of $f$ (the classical Ethier–Norman bound for $r = 2$ used six).

## Depends on

- [Uniqueness in law for the K-allele martingale problem with a general bounded mutation matrix](../../neutral-wright-fisher-martingale-problem/uniqueness-in-law-for-the-k-allele-martingale-pr.md)
- [Well-posedness of the Wright–Fisher martingale problem with mutation](../../neutral-wright-fisher-martingale-problem/well-posedness-of-the-mutation-martingale-proble.md)

## Expansion

The Lindeberg principle in Markov-process form telescopes the difference over generations: $\mathbb{E}f(X(n)) - \mathbb{E}f(Y(n)) = \sum_{k} \mathbb{E}\big[(P^X - P^Y)P_{n-k-1}^X f\big]\,(Y(k))$ with $P^X$, $P^Y$ the one-step kernels. Each one-step difference is a fourth-order Taylor comparison of the multinomial step with the diffusion over unit time, contributing terms of order $\bar u$ and $1/N$, and the derivatives of the diffusion semigroup $P_t^X f$ decay like $e^{-\lambda_m t}$ because the drift is linear and the diffusion coefficient quadratic (so $\mathcal{L}$ maps polynomials of degree $m$ to degree $m$). Summing the geometric series gives the time-uniform bound.

## Sources

- Peng Chen, Jie Xiong, Lihu Xu and Jiayu Zheng, "Quantitative Diffusion Approximation for the Neutral r-Alleles Wright-Fisher Model with Mutations", *Potential Analysis* 64 (2026), 56, <https://doi.org/10.1007/s11118-026-10298-5>. Numbering as in the preprint arXiv:2407.09102v1, <https://arxiv.org/abs/2407.09102v1>: Assumption 2.1, Theorem 2.2, Corollary 2.4 and Theorem 1.1 (comparison).
