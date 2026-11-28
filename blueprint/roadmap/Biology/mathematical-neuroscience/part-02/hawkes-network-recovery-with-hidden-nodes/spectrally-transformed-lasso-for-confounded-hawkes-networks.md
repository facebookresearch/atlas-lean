# Spectrally transformed lasso for confounded Hawkes networks

**Estimator.** In the [confounded Hawkes model](confounded-multivariate-hawkes-process.md), let $X\in\mathbb R^{T\times p}$ be the design of observed integrated histories with singular value decomposition $X=UDV^{\mathsf T}$, singular values $d_1,\dots,d_r$. A spectral transformation is $F=U\operatorname{diag}(\tilde d_1/d_1,\dots,\tilde d_r/d_r)U^{\mathsf T}$; the trim transformation uses $\tilde d_k=\min(\tau,d_k)$ with $\tau$ the median singular value. With $\tilde X=FX$, $\tilde Y_i=FY_i$, estimate

$$(\hat\mu_i,\hat\beta_i)=\arg\min_{\mu_i,\beta_i}\ \tfrac1T\|\tilde Y_i-\mu_i-\tilde X\beta_i\|_2^2+\lambda\|\beta_i\|_1 .$$

Shrinking the top singular directions shrinks $\tilde Xb_i$ when the confounding vector $b_i$ lies near them.

**Theorem (estimation error).** Let $s^*$ be the maximal in-degree among observed units, and $\gamma_{\min},\gamma_{\max}$ the extreme eigenvalues of $Q=\tfrac1T\sum_t(1,x(t)^{\mathsf T})^{\mathsf T}(1,x(t)^{\mathsf T})$. Under the stationarity and boundedness assumptions, if $(\log p)\vee(s^*)^{1/2}=o(T^{1/5})$ and $\lambda=O(\Lambda_{\max}^2(F)\,T^{-2/5})$, then with probability at least $1-c_1p^2T\exp(-c_2T^{1/5})$, for all $i\le p$,

$$\|\beta_i-\hat\beta_i\|_1\le C_1\Lambda_{\max}^2(F)\,\frac{s^*}{\gamma_{\min}^2}\,T^{-2/5}+C_2\Lambda_{\max}^{-2}(F)\,T^{-3/5}\,\|\tilde Xb_i\|_2^2 .$$

The bound does not depend on the number $q$ of hidden units.

**Corollary.** If moreover $\|b_i\|_2^2=O\big(s^*\Lambda_{\max}^2(F)\,T^{-4/5}/(\gamma_{\min}^2\gamma_{\max})\big)$, then $\|\beta_i-\hat\beta_i\|_1=O\big(s^*\Lambda_{\max}^2(F)\,T^{-2/5}/\gamma_{\min}^2\big)$, the fully observed rate.

**Theorem (edge recovery).** If every true edge satisfies $|\beta_{ij}|\ge\beta_{\min}>2\tau$ with $\tau$ of order $s^*\Lambda_{\max}^2(F)T^{-2/5}/\gamma_{\min}^2$, the thresholded estimator $\tilde\beta_{ij}=\hat\beta_{ij}\mathbf 1\{|\hat\beta_{ij}|>\tau\}$ recovers the edge set: $P(\hat S=S)\ge1-c_1p^2T\exp(-c_2T^{1/5})$.

## Depends on

- [Confounded multivariate Hawkes process](confounded-multivariate-hawkes-process.md)

## Expansion

The proof follows the lasso basic inequality on the perturbed model, using restricted strong convexity of $\tilde X$ (the transformation leaves the smallest eigenvalue unchanged) and a martingale concentration bound for $\tfrac1T\int\nu(t)\tilde X(t)$, then splits on whether the confounding term $\tfrac1T\|\tilde Xb_i\|_2^2$ dominates. The corollary uses $\tfrac1T\|\tilde Xb_i\|_2^2\le\Lambda_{\max}^2(F)\gamma_{\max}\|b_i\|_2^2$.

## Sources

- X. Wang, A. Shojaie, "Causal discovery in high-dimensional point process networks with hidden nodes", Entropy 23 (2021) 1622, Sections 3.1 and 4 and Appendix B: Equations (11)–(14), Theorem 1, Corollary 1, Assumption 5, Theorem 2, <https://doi.org/10.3390/e23121622>, PMCID PMC8700240.
