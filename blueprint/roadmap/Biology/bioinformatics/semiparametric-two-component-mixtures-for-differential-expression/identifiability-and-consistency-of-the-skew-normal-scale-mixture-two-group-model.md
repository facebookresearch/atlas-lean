# Identifiability and consistency of the skew-normal scale mixture two-group model

**Model.** Gene-level test statistics $z_1,\dots,z_n$ are modeled as i.i.d. draws from

$$f(z) = \pi\,\phi(z;0,1) + (1-\pi)\,f_{\rm SNSM}(z;\mu,\lambda,G), \qquad f_{\rm SNSM}(z;\mu,\lambda,G) = \int \frac2\sigma\,\phi\Big(\frac{z-\mu}{\sigma}\Big)\Phi\Big(\lambda\frac{z-\mu}{\sigma}\Big)\,dG(\sigma),$$

where $\pi \in (0,1)$ is the proportion of null (non-differentially expressed) genes, $\phi, \Phi$ are the standard normal density and distribution function, $\mu > 0$ is a location, $\lambda \ge 0$ a skewness parameter, and $G$ an arbitrary mixing distribution of scales on $(0,\infty)$. Skew-$t$, skew-slash and skew-contaminated normal alternatives are special cases. Genes are then ranked by the local false discovery rate $\pi\phi(z)/f(z)$.

**Assumptions.** (A1) $\phi(\cdot;0,1)$ is linearly independent of the class $\{f_{\rm SNSM}(\cdot;\mu,\lambda,G) : \mu > 0, \lambda \ge 0\}$ (no finite linear combination of the null and alternative densities vanishes unless all coefficients are zero). (A2) $G$ is supported in $[\ell,\infty)$ for some $\ell > 0$. (A3) $\int_\ell^\infty \log\sigma\,dG(\sigma) < \infty$.

**Theorem (identifiability).** Under (A1), if two parameter sets $(\pi,\mu,\lambda,G)$ and $(\tilde\pi,\tilde\mu,\tilde\lambda,\tilde G)$ with $\mu,\tilde\mu > 0$, $\lambda,\tilde\lambda \ge 0$ define the same density almost everywhere, then they are equal.

**Theorem (consistency).** Under (A1)–(A3), the nonparametric maximum likelihood estimator $(\hat\pi,\hat\mu,\hat\lambda,\hat G)$ is consistent for $(\pi,\mu,\lambda,G)$ (with $\hat G \to G$ weakly).

## Expansion

Linear independence (A1) separates the null proportion: equality of the two mixtures forces the $\phi$ coefficients to agree, hence $\pi = \tilde\pi$, and then equality of the SNSM densities. Identifiability of $(\mu,\lambda,G)$ within the non-null SNSM class is then needed to recover the remaining parameters. Consistency follows Kiefer–Wolfowitz type arguments for nonparametric mixture MLEs: (A2) keeps densities bounded, so the log-likelihood is bounded above; (A3) gives the integrability needed for Wald's argument on a compactified parameter space; and identifiability turns convergence of fitted densities into convergence of parameters.

## Sources

- Sangkon Oh, Geoffrey J. McLachlan, "Differential gene expression analysis via two-component mixture models with a semiparametric alternative", arXiv (2026). Assumptions (A1)–(A3), Theorem 1, Theorem 2. <https://doi.org/10.48550/arXiv.2603.01381>
