# Confounded multivariate Hawkes process

**Linear Hawkes model.** A $p$-variate counting process $N=(N_1,\dots,N_p)$ is a linear Hawkes process if its conditional intensities are

$$\lambda_i(t)=\mu_i+\sum_{j=1}^p\int_0^{t^-}\omega_{ij}(t-s)\,dN_j(s),$$

with background rates $\mu_i$ and transfer functions $\omega_{ij}$. With $\omega_{ij}(t)=\beta_{ij}\kappa_j(t)$ and integrated histories $x_j(t)=\int_0^{t^-}\kappa_j(t-s)\,dN_j(s)$, writing $Y_i(t)=dN_i(t)/dt$ gives the regression form $Y_i(t)=\mu_i+x(t)^{\mathsf T}\beta_i+\epsilon_i(t)$; $\beta_{ij}>0$ is excitation and $\beta_{ij}<0$ inhibition of unit $i$ by unit $j$.

**Hidden components.** If only $p$ of $p+q$ units are recorded, with hidden integrated histories $z(t)\in\mathbb R^q$,

$$Y_i(t)=\mu_i+x(t)^{\mathsf T}\beta_i+z(t)^{\mathsf T}\delta_i+\epsilon_i(t).$$

Let $b_i\in\mathbb R^p$ be the projection coefficient defined by $\operatorname{Cov}\big(x(t),\,z(t)^{\mathsf T}\delta_i-x(t)^{\mathsf T}b_i\big)=0$. Then

$$Y_i(t)=\mu_i+x(t)^{\mathsf T}(\beta_i+b_i)+\nu_i(t),\qquad \nu_i(t)=z(t)^{\mathsf T}\delta_i-x(t)^{\mathsf T}b_i+\epsilon_i(t),$$

with $\nu_i$ uncorrelated with $x$. Regression on observed histories identifies only $\beta_i+b_i$, and $b_i=0$ when $\operatorname{Cov}(x,z)\,\delta_i=0$ (in particular when $\delta_i=0$ or $\operatorname{Cov}(x,z)=0$), and in general $b_i\neq0$ otherwise (the source: "In general, $b_i\neq0$ unless $\mathrm{Cov}(x(t),z(t))=0$"): ignoring hidden units yields spurious or biased edges.

**Stability limits the confounding.** Let $\Omega_{ij}=\int_0^\infty|\omega_{ij}(\Delta)|\,d\Delta$ over all $p+q$ units. Stationarity is assumed via $\Lambda_{\max}(\Omega^{\mathsf T}\Omega)\le\gamma_\Omega^2<1$, together with bounded intensities, bounded integrable kernels, and row sums of $\Omega$ at most $\rho_r<1$ and column sums at most $\rho_c<\infty$. These give $\|b_i\|_1=O(\|\delta_i\|_1)=O(1)$; if the confounding is dense ($\|b_i\|_0$ of order $p$) then $\|b_i\|_2^2=O(1/p)$, small in the high-dimensional regime.

## Expansion

The same phenomenon appears in a three-variable vector autoregression: if a common driver of two observed series is hidden, the conditional mean of one observed series acquires a spurious autoregressive dependence. In a stable Hawkes network the total influence entering a unit is bounded, so a hidden population that touches many observed units can shift each observed coefficient only slightly.

## Sources

- X. Wang, A. Shojaie, "Causal discovery in high-dimensional point process networks with hidden nodes", Entropy 23 (2021) 1622, Sections 2.1, 2.2, 3.1 and 4: Equations (2)–(10), Assumptions 1–4 and the discussion after Corollary 1, <https://doi.org/10.3390/e23121622>, PMCID PMC8700240.
