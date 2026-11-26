# MM-test screening consistency and knockoff FDR control for spatially variable genes

**Setting.** Observe $n$ spots (cells or tissue locations) with expression vectors $\mathbf{x}_i\in\mathbb{R}^p$, each spot belonging to one of $K$ unknown spatial domains with proportions $\alpha_k$. Gene $j$ has domain-specific law $F_{kj}$ with mean $\mu_{kj}$ and variance $\tau_{kj}$; only a mean–variance relation is assumed,

$$\tau_{kj}=V(\mu_{kj};\phi)=V_1(\mu_{kj})+\phi\,V_2(\mu_{kj}),$$

with known $V_1\ge0$, $V_2>0$ (quasi-Poisson: $V_1=0$, $V_2(\mu)=\mu$; quasi-negative-binomial: $V_1(\mu)=\mu$, $V_2(\mu)=\mu^2$). Gene $j$ is spatially variable if $j\in S_1=\{j:\mu_{kj}\ne\mu_{\ell j}\text{ for some }k,\ell\}$, and null if all domain means agree.

For one gene write the quasi-likelihood $Q(x;\mu,\phi)=\int_x^\mu\frac{x-t}{V(t;\phi)}dt$, quasi-density $f=e^{Q}$, and mixture quasi-likelihood $l_n(\boldsymbol\alpha,\boldsymbol\mu,\phi)=\sum_i\log\sum_k\alpha_k f(x_i;\mu_k,\phi)$. A working dispersion $\hat\phi$ uses an auxiliary distance between spots (spatial coordinates in 2D or 3D, or histology-image features): with $\hat\mu_i$ the mean over the $r_n=n^\beta$ nearest neighbours of spot $i$ and $\hat\phi_0=(\hat\tau_0-V_1(\bar x))/V_2(\bar x)$ the pooled dispersion,

$$\hat\phi=\max\Big\{\hat\phi_0-\sqrt{r_n}\,\frac1n\sum_{i=1}^n(\bar x-\hat\mu_i)^2\Big/V_2(\bar x),\ m_\phi\Big\}.$$

After $T_n$ minorize–maximize (EM-type) updates of $(\boldsymbol\alpha,\boldsymbol\mu)$ at fixed $\hat\phi$, the MM-test statistic is

$$\mathrm{MM}_n^{(T_n)}=2\Big\{l_n\big(\boldsymbol\alpha^{(T_n)},\boldsymbol\mu^{(T_n)},\hat\phi\big)-l_n\big(\boldsymbol\alpha_0,(\bar x,\dots,\bar x),\hat\phi\big)\Big\},$$

and genes with $\mathrm{MM}_{nj}^{(T_n)}\ge t_n$ form $\hat S_1(t_n)$.

**Theorem.**

1. (Selection consistency.) Assume uniformly bounded $L_q$ moments, and that the neighbourhood means deviate from the global mean on average by more than $r_n^{-\vartheta}$ for some $\vartheta<1/2$ (the auxiliary distances carry minimal domain information). Let $0<\varpi<1/2-\vartheta$, $r_n^{\vartheta}(\log n)^2<T_n<r_n^{1/2-\varpi}\log n$ and $t_n=r_n^{-\kappa}$ with $-1+3\vartheta<\kappa<5/2$. Then for large $n$, with $s=|S_1|$,

$$\Pr\big(\hat S_1(t_n)\ne S_1\big)\lesssim (p-s)\,r_n^{-c_1q+\beta^{-1}}+s\,r_n^{-c_2q+\beta^{-1}}+o(1),$$

for constants $c_1,c_2>0$ depending only on $\kappa,\vartheta$.

2. (FDR control.) Build knockoff genes by resampling each gene's values with replacement, compute MM statistics on the augmented matrix, inflate the knockoff statistics by $1+1/\log n$, and select genes above the smallest threshold $H_{q_0}$ at which the knockoff-to-original exceedance ratio is at most $q_0$. If in addition null genes have identical means and variances across domains, then $\mathrm{FDR}\le q_0+o(1)$ as $s\to\infty$.

3. (Post-selection clustering.) Under a domain-separation condition, clustering on the selected genes has normalized Hamming error at most $\Pr(\hat S_1\ne S_1)+o(1)$.

## Expansion

The statistic is a likelihood ratio in which only the first two moments are modelled, so it applies to over-dispersed counts without a parametric family. The key device is the working dispersion. Under the null, neighbourhood means stay near the global mean and $\hat\phi\approx\phi$, so the mixture fit gains little and the statistic stays small. Under the alternative, the pooled variance contains the between-domain term $\sum_k\alpha_k(\mu_k-\mu_0)^2$; subtracting a spatially estimated (and $\sqrt{r_n}$-amplified) version of it shrinks $\hat\phi$, which makes the mixture fit markedly better than the single-mean fit. Bounding the number of MM iterations controls how far the non-convex optimization moves, and polynomial moment bounds give the tail probabilities summed over the $p$ genes. Knockoffs by resampling break the domain structure while preserving the marginal law, which yields exchangeability for null genes and the FDR bound without computing $p$-values.

## Sources

- Changhu Wang, Qiyun Huang, Zihao Chen, Jin Liu, "Distribution-free screening of spatially variable genes in spatial transcriptomics", arXiv:2603.09061 (2026): Section 3 (model setup, quasi-likelihood, MM-test statistic, working dispersion, knockoff procedure and threshold), Section 4 (selection consistency theorem, post-selection Hamming error result, FDR theorem; Conditions 1–4 in Appendix B). <https://doi.org/10.48550/arXiv.2603.09061>
