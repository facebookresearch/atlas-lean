# $L^2$ asymptotics of the total external branch length of Beta-coalescents

For a finite measure $\Lambda$ on $[0,1]$ let $\nu(dx) = x^{-2}\Lambda(dx)$ and $\rho(t) = \int_t^1\nu(dx)$. In the $\Lambda$ $n$-coalescent, let $T_i^{(n)}$ be the length of the external branch ending at leaf $i$ and $L_{ext}^{(n)} = \sum_{i=1}^n T_i^{(n)}$ the total external length. Assume

$$\rho(t) = C_0t^{-\alpha} + C_1t^{-\alpha+\zeta} + o(t^{-\alpha+\zeta}), \qquad t \to 0, \quad 1 < \alpha < 2,\ C_0 > 0,\ \zeta > 0,$$

and let $\omega^{(1)} = \sup\{u \ge 0 : \int_y^1(1-x)^{-u}(1-x)\nu(dx) < \infty\ \forall y\in(0,1)\}$ measure the singularity of $\nu$ at $1$. This class contains the Beta$(2-\alpha,\alpha)$-coalescents, for which $n^{\alpha-1}T_1^{(n)}$ converges in law to a random variable $T$.

**Theorem.** Suppose $\alpha - 1 < \zeta$ and $2(\alpha-1) < \omega^{(1)}$. With

$$\mathbb E[T] = \frac{\alpha-1}{C_0\Gamma(2-\alpha)}, \qquad \Delta(\alpha) = \frac{\int_0^1\big((1-x)^{2-\alpha}-1\big)^2\nu(dx)}{3-\alpha}\left(\frac{\alpha-1}{C_0\Gamma(2-\alpha)}\right)^3,$$

1. $\displaystyle\lim_{n\to\infty} n^{3(\alpha-1)}\,\mathrm{Cov}\big(T_1^{(n)},T_2^{(n)}\big) = \Delta(\alpha) > 0$;
2. $\displaystyle\lim_{n\to\infty} n^{3\alpha-5}\,\mathbb E\Big[\big(L_{ext}^{(n)} - n^{2-\alpha}\mathbb E[T]\big)^2\Big] = \frac{\Delta(\alpha)}{2}$, hence $n^{\alpha-2}L_{ext}^{(n)} \to \mathbb E[T]$ in $L^2$.

For the Beta$(2-\alpha,\alpha)$-coalescent, $\mathbb E[T] = \alpha(\alpha-1)\Gamma(\alpha)$ and

$$\lim_{n\to\infty} n^{3\alpha-5}\,\mathbb E\Big[\big(L_{ext}^{(n)} - n^{2-\alpha}\mathbb E[T]\big)^2\Big] = \frac{\big((\alpha-1)\Gamma(\alpha+1)\big)^2\,\Gamma(4-\alpha)}{2(3-\alpha)\,\Gamma(4-2\alpha)}.$$

**Moments of one external branch.** If moreover $\zeta > 1 - 1/\alpha$, then for $0 \le \beta < \alpha/(\alpha-1)$ with $\beta(\alpha-1) < \omega^{(1)}$, $\mathbb E\big[(n^{\alpha-1}T_1^{(n)})^\beta\big] \to \mathbb E[T^\beta]$, while for $\beta \ge \alpha/(\alpha-1)$ these moments diverge.

External branches are positively correlated in the limit, as for the Bolthausen–Sznitman coalescent and unlike Kingman's coalescent, where they are negatively correlated.

## Depends on

- [The Beta-coalescent measure on the unit interval](../merger-rates-and-beta-coalescents/beta-lambda.md)

## Expansion

Conditioning on the first merger, which reduces $n$ blocks to $k$ with probability $p_{n,k}$ after an $\mathrm{Exp}(g_n)$ time with $g_n = \sum_{a\ge2}\binom na\lambda_{n,a} \sim C_0\Gamma(2-\alpha)n^\alpha$, gives linear recursions for $\mathbb E[T_1^{(n)}]$ and $\mathbb E[T_1^{(n)}T_2^{(n)}]$; for instance $\mathbb E[T_1^{(n)}T_2^{(n)}] = 2\mathbb E[T_1^{(n)}]/g_n + \sum_k p_{n,k}\frac{(k-1)_2}{(n)_2}\mathbb E[T_1^{(k)}T_2^{(k)}]$. A general lemma on such recursions turns the expansion of $g_n$ (using the second-order term $C_1$ of $\rho$) into expansions of the solutions, and the leading terms cancel in the covariance, leaving $\Delta(\alpha)n^{3-3\alpha}$. The variance of $L_{ext}^{(n)}$ is $n\,\mathrm{Var}(T_1^{(n)}) + n(n-1)\mathrm{Cov}$ plus a bias term from $\mathbb E[T_1^{(n)}]$; the condition $\zeta > \alpha - 1$ makes the bias negligible at scale $n^{5-3\alpha}$.

## Sources

- Jean-Stéphane Dhersin, Linglong Yuan, "Asymptotic behavior of the total length of external branches for Beta-coalescents", published as "On the total length of external branches for beta-coalescents", *Advances in Applied Probability* 47 (2015), 693–714, <https://doi.org/10.1239/aap/1444308878>; preprint arXiv:1202.5859, <https://doi.org/10.48550/arXiv.1202.5859>. Numbering of the arXiv version: Section 1 (assumption on $\rho$, Theorems 1.1–1.3, Corollary 1.4), Section 2 (Theorem 2.1, Lemmas 2.2–2.4), Section 3.
