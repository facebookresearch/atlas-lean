# Heterozygosity of an admixed population and its lower bound

Fix one locus with $J \ge 2$ allelic types and $K \ge 2$ source populations. Source $k$ has allele-frequency vector $p_k = (p_{k1}, \dots, p_{kJ})$ in the probability simplex $\Delta^{J-1}$, with expected heterozygosity

$$H_k = 1 - \sum_{j=1}^{J} p_{kj}^2 ,$$

and for two sources $k, \ell$ let

$$C_{k\ell} = 1 - p_k \cdot p_\ell = 1 - \sum_{j=1}^{J} p_{kj}\, p_{\ell j}$$

be the probability that one allele drawn from $k$ and one from $\ell$ differ in type, so $C_{kk} = H_k$. Assume no two sources are fixed for the same allele, so $C_{k\ell} > 0$. Let $F_{k\ell} = (H_T - H_S)/H_T$ be the pairwise fixation index of $k$ and $\ell$ pooled with equal weights, where $H_S = (H_k + H_\ell)/2$ and $H_T$ is the heterozygosity of the pooled frequencies $(p_k + p_\ell)/2$.

An admixed population with admixture fractions $\gamma = (\gamma_1, \dots, \gamma_K) \in \Delta^{K-1}$ has allele frequencies $\bar p_j = \sum_k \gamma_k p_{kj}$ and heterozygosity $H_{\mathrm{adm}} = 1 - \sum_j \bar p_j^2$.

**Decomposition.**

$$F_{k\ell} = \frac{2C_{k\ell} - H_k - H_\ell}{2C_{k\ell} + H_k + H_\ell}, \qquad C_{k\ell} = \frac{H_k + H_\ell}{2}\cdot\frac{1 + F_{k\ell}}{1 - F_{k\ell}} \quad (F_{k\ell} < 1),$$

and

$$H_{\mathrm{adm}} = \sum_{k=1}^{K} \gamma_k^2 H_k + 2\sum_{k<\ell} \gamma_k \gamma_\ell C_{k\ell} = \gamma^\top A\, \gamma, \qquad A = (C_{k\ell})_{k,\ell=1}^{K} = \mathbf 1\mathbf 1^\top - P^\top P,$$

where $P$ is the $J \times K$ matrix with columns $p_1, \dots, p_K$. If $F_{k\ell} = 1$ the two sources are fixed for different alleles and $C_{k\ell} = 1$.

**Lower bound (Proposition 3).** Let $H_m = \min_k H_k$. For every $\gamma \in \Delta^{K-1}$,

$$H_{\mathrm{adm}}(\gamma) \ge H_m ,$$

with equality at the vertex of a least heterozygous source. Thus no admixture can be less diverse than its least diverse source.

**Average over random sources (Proposition 13, Corollaries 14–16).** If $p_1, \dots, p_K$ are independent and identically distributed and $\gamma$ is fixed, then

$$\mathbb E[H_{\mathrm{adm}}] = \mathbb E[H_1] + \Big(1 - \sum_{k=1}^{K}\gamma_k^2\Big)\sum_{j=1}^{J}\operatorname{Var}[p_{1j}] \;\ge\; \mathbb E[H_1],$$

maximized over $\gamma$ at $\gamma = (1/K, \dots, 1/K)$. If each $p_k$ is symmetric Dirichlet with concentration $\bar\alpha$, then

$$\mathbb E[H_k] = \Big(1 - \frac1J\Big)\Big(1 - \frac{1}{J\bar\alpha + 1}\Big), \qquad \mathbb E[H_{\mathrm{adm}}] = \Big(1 - \frac1J\Big)\Big(1 - \frac{\sum_k \gamma_k^2}{J\bar\alpha + 1}\Big).$$

## Depends on

- [Wright's hierarchical F-statistics identity](../../wright-s-f-statistics/hierarchical-f-statistics.md)

## Expansion

The formula for $F_{k\ell}$ follows from $H_T = (H_k + H_\ell + 2C_{k\ell})/4$; solving it for $C_{k\ell}$ gives the second identity. Expanding $\sum_j(\sum_k \gamma_k p_{kj})^2$ and using $\sum_k \gamma_k = 1$ gives $H_{\mathrm{adm}} = \gamma^\top A\gamma$. By Cauchy–Schwarz, $p_k \cdot p_\ell \le \sqrt{(1-H_k)(1-H_\ell)} \le 1 - \min(H_k,H_\ell)$, so every entry of $A$ is at least $H_m$. Hence $H_{\mathrm{adm}} \ge H_m(\sum_k\gamma_k)^2 = H_m$. For the expectation, independence gives $\mathbb E[p_{kj}p_{\ell j}] = \mathbb E[p_{1j}]^2$ for $k \ne \ell$; collecting the $\gamma_k^2$ and cross terms leaves the variance term. The Dirichlet case uses $\sum_j \operatorname{Var}[p_{1j}] = (1 - 1/J)/(J\bar\alpha + 1)$.

## Sources

- S. M. Boca, L. Huang and N. A. Rosenberg, "On the heterozygosity of an admixed population", *Journal of Mathematical Biology* 81 (2020), 1217–1250, <https://doi.org/10.1007/s00285-020-01531-9> (PMC7710588), Sections 2–3 (Definitions 1–2, Equations 1–4 and 8–10, Proposition 3) and Appendix 3 (Proposition 13, Corollaries 14–16).
