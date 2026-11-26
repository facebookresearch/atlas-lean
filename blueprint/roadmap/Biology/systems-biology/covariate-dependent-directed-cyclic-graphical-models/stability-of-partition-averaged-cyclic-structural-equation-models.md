# Stability of partition-averaged cyclic structural equation models

**Model.** For cells or spots $i$ with gene expression $Y_i \in \mathbb{R}^p$ and covariates $X_i \in \mathbb{R}^q$ (spatial coordinates), the covariate-dependent structural equation model is

$$Y_i = M(X_i) + B(X_i)\,Y_i + E_i,$$

with intercepts $M(\cdot)$, regulatory matrix $B(\cdot)$ with zero diagonal ($B_{kj}(x) \neq 0$ draws the edge $j \to k$, cycles allowed) and independent non-Gaussian (Laplace) noises $E_i$, which make Markov-equivalent cyclic graphs distinguishable. A matrix is *stable* if all its eigenvalues have modulus less than one, so that $I - B$ is invertible and the system is the equilibrium of the feedback dynamics; a function $B(\cdot)$ is stable if $B(x)$ is stable for every $x$.

**Hierarchy.** Instead of parametrizing $B(\cdot)$ directly, draw a covariate-dependent random partition $S_{[L_n]}$ of the units from a product partition model with covariates, $P(S_{[L_n]} \mid X) \propto \prod_\ell g(X_{S_\ell})\,c(S_\ell)$ with cohesion $c(S) = \alpha(|S|-1)!$, and give each cluster its own matrix $B_\ell$ under a *stable spike-and-slab* prior

$$P(B_\ell \mid \gamma_\ell,\eta_\ell) \propto I(B_\ell \in \mathbb{S}_p)\prod_{j\neq k}\big\{\gamma_{\ell jk}N(B_{\ell jk} \mid 0,\eta_\ell) + (1-\gamma_{\ell jk})N(B_{\ell jk} \mid 0,\nu_0\eta_\ell)\big\},$$

where $\mathbb{S}_p$ is the set of stable $p\times p$ matrices. Set $B(X_i) = B_{\xi_i}$ for the cluster label $\xi_i$; the likelihood is $\prod_i P_E\big((I - B_{\xi_i})Y_i - M_{\xi_i}\big)\,|\det(I - B_{\xi_i})|$.

**Proposition (Section 2.5).** Marginalizing the partition, the covariate-dependent graph is stable with probability one: $P(B(X_i) \in \mathbb{S}_p\ \forall i) = 1$, and for a new location the posterior predictive satisfies

$$\Pr\big(B(X_{n+1}) \in \mathbb{S}_p \mid Y_{[n]},X_{[n]},X_{n+1}\big) = 1.$$

## Expansion

The proof conditions on the cluster label: given $\xi_{n+1} = \ell$, $B(X_{n+1}) = B_\ell$, which is stable by the truncation in its prior, and averaging over $\xi_{n+1}$ preserves probability one. The point of the construction is that stability is a non-convex spectral constraint that is hard to impose on splines or Gaussian processes over $x$, but trivial to impose cluster by cluster. Posterior means of $B(x)$ obtained by averaging over partitions vary smoothly in space, while every sampled graph remains a valid stable cyclic model. The intractable truncation constants cancel because the hyperpriors on $(\gamma_\ell,\eta_\ell)$ and the edge probability are chosen to contain them (a cascade prior), leaving Bernoulli, inverse-gamma and beta full conditionals.

## Sources

- Trisha Dawn and Yang Ni, *Spatially Varying Gene Regulatory Networks via Bayesian Nonparametric Covariate-Dependent Directed Cyclic Graphical Models*, arXiv:2512.11732 (2025). <https://doi.org/10.48550/arXiv.2512.11732> Section 2.1 (covariate-dependent SEM, stable functions), Sections 2.3–2.4 (partition prior, stable spike-and-slab and cascade priors) and the proposition of Section 2.5 (partition averaging).
