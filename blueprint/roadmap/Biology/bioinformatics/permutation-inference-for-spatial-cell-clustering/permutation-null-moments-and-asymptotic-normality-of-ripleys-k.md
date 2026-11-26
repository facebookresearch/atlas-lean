# Permutation-null moments and asymptotic normality of Ripley's $K$

**Setting.** A tissue sample of area $|A|$ contains $n$ cells at fixed locations $c_1,\dots,c_n$, of which $m$ are immune cells and the rest background cells. For a radius $r$, let $W_{ij}(r)=\mathbf 1\{d(c_i,c_j)\le r\}\,e_{ij}$ with edge corrections $e_{ij}$, taken symmetric. With label vector $x\in\{0,1\}^n$ marking immune cells, **Ripley's $K$** for the immune cells is

$$\hat K(r)=\frac{|A|}{m(m-1)}\,x^\top W(r)\,x=\frac{|A|}{m(m-1)}\sum_{i\ne j}W_{ij}(r)\,\mathbf 1\{g_i=g_j=1\}.$$

For two immune types with counts $m_1,m_2$ and label vectors $x_1,x_2$, the bivariate version is $\hat K_c(r)=\frac{|A|}{m_1m_2}x_1^\top W(r)x_2$. Tissue architecture makes cell density inhomogeneous, so the complete-spatial-randomness benchmark $\pi r^2$ overstates clustering. The null hypothesis is instead *proportional intensity*: immune cells follow the same spatial intensity as all cells. Under it, $K$ is compared with its distribution under uniformly random relabelling, $x\mapsto Px$, with the locations held fixed.

Write

$$R_0=\sum_{i\ne j}W_{ij},\qquad R_1=\sum_{i\ne j}W_{ij}^2,\qquad R_2=\sum_{i\ne j\ne u}W_{ij}W_{iu},\qquad R_3=\sum_{i,j,u,v\ \text{distinct}}W_{ij}W_{uv},$$

and $(x)_k=x(x-1)\cdots(x-k+1)$ for falling factorials.

**Theorem.**

1. *(Exact permutation moments.)*

$$\mathbb E K(r)=\mathbb E K_c(r)=\frac{|A|}{n(n-1)}R_0,$$

$$\operatorname{Var}K(r)=\frac{|A|^2}{m^2(m-1)^2}\Big\{2R_1\frac{(m)_2}{(n)_2}+4R_2\frac{(m)_3}{(n)_3}+R_3\frac{(m)_4}{(n)_4}\Big\}-(\mathbb EK)^2,$$

$$\operatorname{Var}K_c(r)=\frac{|A|^2}{m_1^2m_2^2}\Big\{R_1\frac{m_1m_2}{(n)_2}+R_2\frac{m_1m_2(m_1+m_2-2)}{(n)_3}+R_3\frac{m_1m_2(m_1-1)(m_2-1)}{(n)_4}\Big\}-(\mathbb EK_c)^2 .$$

The null expectation equals Ripley's $K$ computed on all cells. So the adjusted statistic $\tilde K=\hat K-\mathbb EK$ measures clustering of immune cells relative to the background tissue.
2. *(Asymptotic normality.)* Let $\bar W=R_0/(n(n-1))$, $\tilde W_{ij}=(W_{ij}-\bar W)\mathbf 1_{i\ne j}$ and $\tilde W_{i\cdot}=\sum_j\tilde W_{ij}$. Assume (i) $\sum_i|\tilde W_{i\cdot}|^h=o\big((\sum_i\tilde W_{i\cdot}^2)^{h/2}\big)$ for all integers $h>2$ (no dominating cell), and (ii) $\sum_{i\ne j}\tilde W_{ij}^2=o\big(\sum_i\tilde W_{i\cdot}^2\big)$. Then as $n\to\infty$ with $m/n$, $m_1/n$, $m_2/n$ converging in $(0,1)$, the standardized statistics

$$Z_K=\frac{\hat K-\mathbb EK}{\sqrt{\operatorname{Var}K}},\qquad Z_{K_c}=\frac{\hat K_c-\mathbb EK_c}{\sqrt{\operatorname{Var}K_c}}$$

converge in distribution to $N(0,1)$ under the permutation null. The conditions hold when the $\tilde W_{ij}$ are of constant order.

This replaces thousands of Monte Carlo permutations by closed-form moments. That gives a scalable test of immune-cell clustering and colocalization that is robust to tissue inhomogeneity, applied for example to ovarian cancer spatial proteomics.

## Expansion

Under a uniform relabelling, the immune labels form a uniformly random $m$-subset of the $n$ cells. The probability that a fixed ordered pair is all-immune is $(m)_2/(n)_2$, which gives $\mathbb EK$ by linearity. For the second moment, expand $\big(\sum_{i\ne j}W_{ij}\mathbf 1_{ij}\big)^2$ into products over pairs sharing two indices, one index, or none. These have probabilities $(m)_2/(n)_2$, $(m)_3/(n)_3$ and $(m)_4/(n)_4$ of being all-immune, and their weight sums are $2R_1$, $4R_2$ and $R_3$ by symmetry of $W$. The bivariate case is the same computation with two disjoint random subsets. Normality follows from a combinatorial central limit theorem for permutation quadratic forms. After centering, the statistic is dominated by the linear part $\sum_i\tilde W_{i\cdot}g_i$, whose moment conditions are (i), while (ii) makes the purely quadratic remainder negligible.

These are the permutation-moment theorem and the asymptotic-normality theorem of Section 2 of the source.

## Sources

- J. Wrobel, H. Song, "A robust, scalable K-statistic for quantifying immune cell clustering in spatial proteomics data", arXiv:2412.08498 (2024). <https://doi.org/10.48550/arXiv.2412.08498>
