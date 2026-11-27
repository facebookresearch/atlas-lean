# Expected number of real roots of random polynomials from multiplayer games

**Setting.** In an infinite population playing a symmetric $(n+1)$-player game with two strategies $A$ and $B$, let $a_i$ ($b_i$) be the payoff to an $A$- ($B$-) player whose $n$ co-players include $i$ $A$-players, and let $\xi_i = a_i - b_i$ be the gain sequence. With $y$ the frequency of $A$, the internal equilibria of the replicator dynamics are the roots $y \in (0,1)$ of $\sum_{i=0}^n \xi_i\binom{n}{i}y^i(1-y)^{n-i} = 0$; with $x = y/(1-y)$ they are the positive roots of

$$P_n(x) = \sum_{i=0}^n \xi_i\binom{n}{i}x^i.$$

For random games with $\xi_i$ i.i.d. standard normal, the expected number of internal equilibria is half the expected number $\mathbb E N_n$ of real roots. More generally consider

$$P_n^{(\gamma)}(x) = \sum_{i=0}^n \xi_i\binom{n}{i}^{\gamma}x^i, \qquad P_n^{(\alpha,\beta)}(x) = \sum_{i=0}^n \binom{n+\alpha}{n-i}^{1/2}\binom{n+\beta}{i}^{1/2}\xi_i x^i,$$

with $\gamma > 0$, $\alpha,\beta > -1$; the game polynomial is $\gamma = 1$, or $\alpha = \beta = 0$.

**Theorem.**
1. As $n \to \infty$,

$$\mathbb E N_n^{(\gamma)} \sim \sqrt{2\gamma n}, \qquad \mathbb E N_n^{(\alpha,\beta)} \sim \sqrt{2n}.$$

In particular a random $(n+1)$-player two-strategy game has on average $\sim\sqrt{n/2}$ internal equilibria, and there is a discontinuity at $\gamma = 0$, where the Kac polynomial gives $\mathbb E N_n \sim \frac{2}{\pi}\ln n$.
2. For $n = 1$, $P_1^{(\alpha,\beta)}$ is almost surely a nonconstant linear polynomial, so $\mathbb E N_1^{(\alpha,\beta)} = 1$. For every $n \ge 2$ and $\alpha > -1$,

$$\frac{2}{\pi}\sqrt{\frac{n(n+2\alpha)}{2n+2\alpha-1}} \le \mathbb E N_n^{(\alpha,\alpha)} \le \frac{2\sqrt n}{\pi}\left(1 + \ln 2 + \frac12\ln\frac{n+\alpha}{1+\alpha}\right),$$

and $\sqrt n\,\frac{1 - s_{n}}{1 + s_{n}} \le \mathbb E N_n^{(\alpha,\alpha)} \le \sqrt n\,\frac{1+s_{n}}{1-s_{n}}$, where $s_n \in (0,1)$ is the largest root of the degree-$n$ Jacobi polynomial $J_n^{(\alpha,\alpha)}(x) = \sum_{i=0}^n \binom{n+\alpha}{n-i}\binom{n+\alpha}{i}\big(\frac{x-1}{2}\big)^i\big(\frac{x+1}{2}\big)^{n-i}$. For $\alpha = \beta$ the zeros of $J_n^{(\alpha,\alpha)}$ are symmetric about $0$, which the bound uses; without this symmetry the largest zero need not be positive (for $n = 1$, $\alpha = 2$, $\beta = 0$ it is $-1/2$), and no bound of this form is claimed for $\alpha \ne \beta$.

## Expansion

By the Kac–Rice formula, $\mathbb E N_n = \frac{1}{\pi}\int_{\mathbb R}\frac{\sqrt{A_n M_n - B_n^2}}{M_n}\,dx$, where $M_n(x) = \sum_i c_i^2 x^{2i}$ is the variance of $P_n(x)$ and $A_n, B_n$ are the corresponding second moments involving the derivative. For binomial-power coefficients the sum $M_n$ is dominated by a Gaussian window of indices around $i \approx n x^{1/\gamma}/(1 + x^{1/\gamma})$ and a Laplace-method evaluation of $M_n$ and $A_nM_n - B_n^2$ on that window, followed by integration over $x$, gives $\sqrt{2\gamma n}$; the region of small $x$ contributes only $o(\sqrt n)$. The finite-$n$ bounds for $P_n^{(\alpha,\alpha)}$ come from expressing the variance $M_n$ through the Jacobi polynomial, $M_n(x) = (1-x^2)^n J_n^{(\alpha,\alpha)}\big(\frac{1+x^2}{1-x^2}\big)$, so that the symmetric zeros $\pm s_k$ of $J_n^{(\alpha,\alpha)}$ give $M_n(x) = m_n\prod_k (x^2 + r_k)$ with $r_k = (1-s_k)/(1+s_k)$ and $r_k r_{n+1-k} = 1$, which bounds the Kac–Rice density between multiples of $1/(x^2 + r_1)$ and $1/(x^2 + r_n)$. Equilibria of random multiplayer games are therefore far more numerous than for Kac-type polynomials but still a vanishing fraction of the $n$ possible.

## Sources

- V. H. Can, M. H. Duong and V. H. Pham, "On the expected number of real roots of random polynomials arising from evolutionary game theory", Communications in Mathematical Sciences 20 (2022), 1613–1636, <https://doi.org/10.4310/cms.2022.v20.n6.a7>; numbering as in arXiv:2010.14198: Theorems 1.1 and 1.2.
