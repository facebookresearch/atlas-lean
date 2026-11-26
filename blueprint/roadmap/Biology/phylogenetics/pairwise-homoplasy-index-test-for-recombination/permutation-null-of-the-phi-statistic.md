# Permutation null distribution of the pairwise homoplasy index

Let $M$ be a symmetric $n\times n$ [refined incompatibility matrix](refined-incompatibility-and-the-phi-statistic.md) and $1 \le k$ with $n \ge 2k$. Let $\sigma$ be a uniformly random permutation of $\{1, \dots, n\}$, $X = (M_{\sigma(i)\sigma(j)})$ the permuted matrix, and $\Phi_w(X)$ the pairwise homoplasy index computed on $X$. Under the null hypothesis of no recombination all sites share one history, so the site order is exchangeable and $\Phi_w(X)$ has the null law of the statistic. Then

1. for distinct $a \ne b$, $\mathbb E[X_{ab}] = \dfrac{1}{n(n-1)}\sum_{i \ne j} M_{ij}$, hence

$$\mathbb E_0[\Phi_w] = \frac{1}{n(n-1)}\sum_{i\ne j} M_{ij},$$

the mean off-diagonal entry of $M$;
2. $\operatorname{Var}_0[\Phi_w]$ has an explicit closed form in terms of sums of entries, squared entries and row sums of $M$, computable in $O(n^2)$ time.

With $\mu' = \mathbb E_0[\Phi_w]$, $\sigma^2 = \operatorname{Var}_0[\Phi_w]$ and observed value $\tau$, the permutation $p$-value $\Pr(\Phi_w(X) \le \tau)$ is approximated by the normal tail

$$P_N = \int_{-\infty}^{\tau} \frac{1}{\sigma\sqrt{2\pi}}\, e^{-(x - \mu')^2/(2\sigma^2)}\,dx .$$

## Depends on

- [Refined incompatibility and the pairwise homoplasy index](refined-incompatibility-and-the-phi-statistic.md)

## Expansion

Any ordered pair of distinct indices is mapped by a uniform permutation to each ordered pair of distinct indices with probability $1/(n(n-1))$ (Appendix A, Lemma 1), giving item 1; linearity of expectation over the $k(2n-k-1)/2$ averaged cells gives the mean. The variance requires counting pairs of cells sharing zero or one index within the band, solved by a recurrence (Appendix A, Theorem 1). Normality is a heuristic justified by the statistic being a mean of many matrix entries; simulations show close agreement with full permutation $p$-values.

## Sources

- T. C. Bruen, H. Philippe, D. Bryant, "A Simple and Robust Statistical Test for Detecting the Presence of Recombination", Genetics 172 (2006), 2665–2681, <https://doi.org/10.1534/genetics.105.048975> (PMC1456386).
