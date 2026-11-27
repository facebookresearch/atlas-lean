# $L^2$ asymptotics of the total external branch length of Beta-coalescents

Fix $1 < \alpha < 2$ and consider the Beta$(2-\alpha,\alpha)$-coalescent, the $\Lambda$-coalescent with $\Lambda(dx) = \frac{x^{1-\alpha}(1-x)^{\alpha-1}}{\Gamma(2-\alpha)\Gamma(\alpha)}\,dx$ on $[0,1]$. In its restriction to $n$ leaves, let $T_i^{(n)}$ be the length of the external branch ending at leaf $i$ and $L_{ext}^{(n)} = \sum_{i=1}^n T_i^{(n)}$ the total external length. Then $n^{\alpha-1}T_1^{(n)}$ converges in law to a random variable $T$ with $\mathbb E[T] = \alpha(\alpha-1)\Gamma(\alpha)$. Let

$$\Delta(\alpha) = \frac{\big((\alpha-1)\Gamma(\alpha+1)\big)^2}{3-\alpha}\left(\frac{\Gamma(4-\alpha)}{\Gamma(4-2\alpha)} - \frac{2}{\Gamma(2-\alpha)}\right).$$

**Theorem.**

1. $\displaystyle\lim_{n\to\infty} n^{3(\alpha-1)}\,\mathrm{Cov}\big(T_1^{(n)},T_2^{(n)}\big) = \Delta(\alpha) > 0$;
2. $\displaystyle\lim_{n\to\infty} n^{3\alpha-5}\,\mathbb E\Big[\big(L_{ext}^{(n)} - n^{2-\alpha}\mathbb E[T]\big)^2\Big] = \Delta(\alpha)$, hence $n^{\alpha-2}L_{ext}^{(n)} \to \mathbb E[T]$ in $L^2$.

Equivalently, with $\nu(dx) = x^{-2}\Lambda(dx)$, $\Delta(\alpha) = \frac{1}{3-\alpha}\,\mathbb E[T]^3\int_0^1\big((1-x)^{2-\alpha}-1\big)^2\nu(dx)$.

The limit in item 2 is $\Delta(\alpha)$, as in Theorem 1.1(i) of the published version; Theorem 1.1 of arXiv:1202.5859v3 gives $\Delta(\alpha)/2$, which contradicts that version's Remark 1.3, where the covariance term is the dominant one. The closed form printed in Theorem 1.1 of both versions omits the $-\frac{2}{\Gamma(2-\alpha)}$ term.

**Moments of one external branch.** For $0 \le \beta < \alpha/(\alpha-1)$, $\mathbb E\big[(n^{\alpha-1}T_1^{(n)})^\beta\big] \to \mathbb E[T^\beta]$, while for $\beta \ge \alpha/(\alpha-1)$ these moments diverge.

External branches are positively correlated in the limit, as for the Bolthausen–Sznitman coalescent and unlike Kingman's coalescent, where they are negatively correlated.

## Depends on

- [The Beta-coalescent measure on the unit interval](../merger-rates-and-beta-coalescents/beta-lambda.md)
- [Limit law of an external branch length in the Beta-coalescent](../external-branches-of-beta-coalescents/limit-law-of-an-external-branch-length-in-the-beta-coalescent.md)

## Expansion

Conditioning on the first merger, which reduces $n$ blocks to $k$ with probability $p_{n,k}$ after an $\mathrm{Exp}(g_n)$ time with $g_n = \sum_{a\ge2}\binom na\lambda_{n,a} \sim C_0\Gamma(2-\alpha)n^\alpha$, where $\rho(t) = \int_t^1\nu(dx) = C_0t^{-\alpha} + O(t^{1-\alpha})$ and $C_0 = 1/(\alpha\Gamma(2-\alpha)\Gamma(\alpha))$, gives linear recursions for $\mathbb E[T_1^{(n)}]$ and $\mathbb E[T_1^{(n)}T_2^{(n)}]$; for instance $\mathbb E[T_1^{(n)}T_2^{(n)}] = 2\mathbb E[T_1^{(n)}]/g_n + \sum_k p_{n,k}\frac{(k-1)_2}{(n)_2}\mathbb E[T_1^{(k)}T_2^{(k)}]$. A general lemma on such recursions turns the expansion of $g_n$ (using the second-order term of $\rho$) into expansions of the solutions, and the leading terms cancel in the covariance, leaving $\Delta(\alpha)n^{3-3\alpha}$. The mean square error of $L_{ext}^{(n)}$ is $n\,\mathrm{Var}(T_1^{(n)}) + n(n-1)\mathrm{Cov}(T_1^{(n)},T_2^{(n)}) + \big(n\mathbb E[T_1^{(n)}] - n^{2-\alpha}\mathbb E[T]\big)^2$; the covariance term is of order $n^{5-3\alpha}$ and dominates, since $n\,\mathrm{Var}(T_1^{(n)}) = O(n^{3-2\alpha})$ and the bias term is $O(n^{6-4\alpha})$.

## Sources

- Jean-Stéphane Dhersin, Linglong Yuan, "On the total length of external branches for beta-coalescents", *Advances in Applied Probability* 47 (2015), 693–714, <https://doi.org/10.1239/aap/1444308878>, Theorems 1.1–1.3, which are stated for the Beta$(2-\alpha,\alpha)$-coalescents; preprint "Asymptotic behavior of the total length of external branches for Beta-coalescents", arXiv:1202.5859, <https://doi.org/10.48550/arXiv.1202.5859>. Numbering of the arXiv version: Section 1 (assumption on $\rho$, Theorems 1.1–1.3, Remarks 1.2–1.3, Corollary 1.4), Section 2 (Theorem 2.1, Lemmas 2.2–2.4), Section 3.
