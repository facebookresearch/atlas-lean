# Gene-set-structured factor loadings and consistency of empirical Bayes shrinkage

**Model.** Let $Y\in\mathbb R^{n\times p}$ hold expression of $p$ genes in $n$ samples ($p\gg n$). Each sample follows the Gaussian factor model

$$y_i=\Lambda\eta_i+\epsilon_i,\qquad \eta_i\sim\mathcal N_k(0,I_k),\quad \epsilon_i\sim\mathcal N_p(0,\sigma^2I_p),$$

so $y_i\sim\mathcal N_p(0,\Lambda\Lambda^\top+\sigma^2I_p)$. Annotated gene sets enter through a binary membership matrix $C\in\{0,1\}^{p\times q}$ and the decomposition

$$\Lambda=C\Gamma+\Psi,\qquad \Psi\in\mathcal N(C^\top)\ \ (\text{columns of }\Psi\perp\text{column space of }C),$$

which gives $\operatorname{cov}(y_i)=C\Gamma\Gamma^\top C^\top+\Psi\Psi^\top+\sigma^2I_p$: a known-pathway low-rank part, a novel-pathway low-rank part, and noise. With orthonormal bases $B_{\mathcal C},B_{\mathcal N}$ of the column space of $C$ and its orthogonal complement, $\Lambda=B_{\mathcal C}\Lambda_{\mathcal C}+B_{\mathcal N}\Lambda_{\mathcal N}$, and the rows receive separate Gaussian shrinkage priors

$$\lambda_{\mathcal C,l}\mid\sigma^2\sim\mathcal N_k(0,\tau_\Gamma^2\sigma^2I_k),\qquad \lambda_{\mathcal N,l'}\mid\sigma^2\sim\mathcal N_k(0,\tau_\Psi^2\sigma^2I_k).$$

**Empirical Bayes hyperparameters.** With $U D V^\top$ the rank-$k$ truncated SVD of $Y$ (so $\widehat M=\sqrt nU$ pre-estimates the factors), $P_C$ the projection onto the column space of $C$,

$$\hat\sigma^2=\frac{\|(I_n-UU^\top)Y\|_2^2}{(n-k)p},\quad L_{\mathcal C}=\frac{\|P_CVD\|_F^2}{n},\quad L_{\mathcal N}=\frac{\|(I_p-P_C)VD\|_F^2}{n},$$

$$\hat\tau_\Gamma^2=\frac{L_{\mathcal C}}{kq\hat\sigma^2},\qquad \hat\tau_\Psi^2=\frac{L_{\mathcal N}}{k(p-q)\hat\sigma^2}.$$

Given $\widehat M$ the model is conjugate: each loading row has a Gaussian posterior with mean $\widehat M^\top y^{(l)}/(n+\tau^{-2})$, computed in parallel over genes without MCMC.

**Theorem (collapse onto the active component).** Suppose the data follow the model with true loadings $\Lambda_0=C\Gamma_0+\Psi_0$, $C\Gamma_0\perp\Psi_0$, noise variance $\sigma_0^2$, $p=p_n\to\infty$ with $\log p_n/n=O(1)$, singular values $s_l(\Lambda_0)\asymp\sqrt p$ for $l\le k$, and known $k$. Then, as $n\to\infty$:
- if $\Psi_0=0$ (no novel pathways), $\hat\tau_\Psi\to0$ in probability, so the model collapses to $\Lambda=C\Gamma$;
- if $\Gamma_0=0$ (no annotated pathways active), $\hat\tau_\Gamma\to0$ in probability.

Along the way, $\hat\sigma^2=\sigma_0^2+O_p(n^{-1/2}+p^{-1/2})$, and $L_{\mathcal C}$, $L_{\mathcal N}$ estimate $\|C\Gamma_0\|_2^2$ and $\|\Psi_0\|_2^2$ with explicit error bounds.

## Expansion

The orthogonality constraint makes $(\Gamma,\Psi)$ identifiable: otherwise $C\Gamma_0$ could be absorbed into $\Psi$. Projecting the data onto the column space of $C$ and its complement splits the likelihood into independent pieces, which is why the two shrinkage levels can be set separately. The estimators match prior expectations, $\mathbb E\|\Lambda_{\mathcal C}\|_F^2=\tau_\Gamma^2\sigma^2qk$, to plug-in signal energies. Under the spiked-singular-value assumption the leading left singular space of $Y$ converges to that of the signal ($\|UU^\top-U_0U_0^\top\|\lesssim n^{-1}+p^{-1}$), so when a component is absent its projected energy is pure noise of order $(p-q)$ or $q$ times $o(1)$ relative to the normalization, forcing the corresponding $\hat\tau\to0$.

## Sources

- Lorenzo Mauri, Federica Stolf, Amy H. Herring, Cameron Miller, "Pathway-based Bayesian factor models for 'omics data", arXiv:2601.13419 (2026): Sections 2.1–2.4 (model, priors, posterior, hyperparameters), Assumptions 1–4 and Theorem 1 (Section 2.5), supplementary Propositions 1–5. <https://doi.org/10.48550/arXiv.2601.13419>
