# Blockwise skew-product representation of the Wright–Fisher diffusion

**Setting.** Consider the $HK$-type neutral Wright–Fisher diffusion with parent-independent mutation on the simplex $\Delta_{HK}$, types grouped into $H$ marks of $K$ types each, with generator

$$\mathcal B^K f(z) = \frac12 \sum_{h,k=1}^H \sum_{i,j=1}^K z_{h,i}(\delta_{hk}\delta_{ij} - z_{k,j}) \frac{\partial^2 f}{\partial z_{h,i}\partial z_{k,j}} + \frac12 \sum_{h=1}^H \sum_{i=1}^K \Bigl(\frac{\theta_h}{K} - |\theta|\, z_{h,i}\Bigr)\frac{\partial f}{\partial z_{h,i}},$$

where $|\theta| = \sum_h \theta_h$.

**Theorem.** Let $W$ be the $H$-type Wright–Fisher diffusion on $\Delta_H$ with generator

$$\mathcal A_0 f(w) = \frac12 \sum_{h,k} w_h(\delta_{hk} - w_k) \partial_{hk} f + \frac12 \sum_h (\theta_h - |\theta| w_h)\, \partial_h f,$$

and, independently, let $\tilde X_1, \dots, \tilde X_H$ be independent $K$-type Wright–Fisher diffusions with mutation parameters $\theta_h/K$ (total $\theta_h$). Put

$$\mathcal X_h(t) = \tilde X_h\Bigl(\int_0^t \frac{ds}{W_h(s)}\Bigr), \qquad h = 1, \dots, H.$$

Then $(W, \mathcal X_1, \dots, \mathcal X_H)$ solves a well-posed martingale problem, and if $Z^K$ solves the martingale problem for $\mathcal B^K$ started in the interior with $W_h(0) = \sum_i Z^K_{h,i}(0)$, then

$$Z^K_{h,i}(t) \stackrel{d}{=} W_h(t)\, \mathcal X_{h,i}(t) \quad \text{jointly in } (h, i, t).$$

That is, the mark masses evolve autonomously as an $H$-type Wright–Fisher diffusion, and within each mark the renormalised frequencies are an independent Wright–Fisher diffusion run on the random clock $\int_0^t W_h(s)^{-1} ds$.

## Expansion

The result is the dynamic counterpart of the aggregation–renormalisation property of Dirichlet laws: if $\zeta \sim \mathrm{Dir}_{HK}(\theta_1/K, \dots, \theta_H/K)$ (each repeated $K$ times), the block sums $\upsilon_h = \sum_i \zeta_{h,i}$ are $\mathrm{Dir}_H(\theta_1, \dots, \theta_H)$ and the renormalised blocks $\zeta_{h,\cdot}/\upsilon_h$ are independent $\mathrm{Dir}_K(\theta_h/K, \dots)$, independent of $\upsilon$. A block of mass $w_h$ has internal resampling variance of order $1/w_h$ relative to its own frequencies, which is exactly the time change $1/W_h$.

## Sources

- C. Costantini, M. Ruggiero, "Multiple Poisson-Dirichlet diffusions on generalized Kingman simplices", arXiv:2602.20266 (2026), Proposition 2.1, Theorems 2.3, 2.4 and 2.8, Corollary 2.5, <https://doi.org/10.48550/arXiv.2602.20266>.
