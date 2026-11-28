# Central limit theorems for the admixture model MLE

**Setting.** In the admixture model, genotypes $X_{i,m}\sim\mathrm{Bin}(2,\langle q_{i,\cdot},p_{\cdot,m}\rangle)$ are independent across individuals $i$ and bi-allelic markers $m$, with ancestry vectors $q_{i,\cdot}$ in the simplex and allele frequencies $p_{k,m}$ for $K$ ancestral populations. Estimate the ancestries of individuals $1,\dots,N_C$ and the frequencies at markers $1,\dots,M_C$, treating the remaining parameters as known, and let $\bar\Gamma(q,p)$ be the block-diagonal averaged Fisher information: for individual $i$, $\bar\Gamma_{(q,q),i}=\lim_M -\frac1M\sum_m\mathbb{E}\,\partial^2_{q_{i,1..K-1}}\ell(q,p\mid X_{i,m})$, and for marker $m$, $\bar\Gamma_{(p,p),m}=\lim_N-\frac1N\sum_i\mathbb{E}\,\partial^2_{p_{1..K,m}}\ell(q,p\mid X_{i,m})$.

**Assumption.** True ancestries and frequencies lie in $[\epsilon,1-\epsilon]$; there are infinitely many disjoint $(K-1)$-element linearly independent subsets of the vectors $(p_{1,m}-p_{K,m},\dots,p_{K-1,m}-p_{K,m})$ and infinitely many disjoint $K$-element linearly independent subsets of the ancestry vectors; the averages of $2/(c^0_{i,m}(1-c^0_{i,m}))^3$ over $i$ and over $m$ stay finite; and the MLE is unique.

**Theorem (open parameter space).** Under this assumption, if $\bar\Gamma(\tilde q^0,\tilde p^0)$ is positive definite on the interior parameter set, then

$$
\Bigl(\sqrt M\,(\hat Q^{N_C}-q^0),\ \sqrt N\,(\hat P^{M_C}-p^0)\Bigr)\ \Longrightarrow\ \mathcal N\bigl(0,\bar\Gamma^{-1}(\tilde q^0,\tilde p^0)\bigr)\qquad(N,M\to\infty).
$$

**Theorem (boundary).** Let $N=1$ with known allele frequencies, assume the linear-independence condition on frequency differences, $q^0_K>0$, positive definite information $\bar\Gamma(q^0)$, and that only finitely many $c^0_m$ lie within $\epsilon$ of $\{0,1\}$. With $\mathcal K_{min}=\{k<K:q^0_k=0\}$, $\mathcal K_{max}=\{k<K:q^0_k=1\}$, the cone $\Lambda=\{v\in\mathbb{R}^{K-1}:v_j\le0\ (j\in\mathcal K_{max}),\ v_i\ge0\ (i\in\mathcal K_{min})\}$, $Z\sim\mathcal N(0,\bar\Gamma^{-1}(q^0))$ and

$$
\hat\lambda=\arg\min_{\lambda\in\Lambda}(\lambda-Z)^\top\bar\Gamma(q^0)(\lambda-Z),
$$

one has $\sqrt M\,(\hat Q^1-q^0)\Rightarrow\hat\lambda$ as $M\to\infty$.

## Depends on

- [Consistency of the admixture model MLE](consistency-of-the-admixture-model-mle.md)

## Expansion

Each ancestry parameter is informed by all $M$ markers and each frequency parameter by all $N$ individuals, which explains the different rates $\sqrt M$ and $\sqrt N$ and the block-diagonal limiting information. Given consistency (and uniqueness, which removes label switching and other reparametrizations), a second-order Taylor expansion of the score with a uniform law of large numbers for the observed information gives the Gaussian limit. When the true ancestry lies on the boundary of the simplex, as ADMIXTURE estimates often do, the local parameter space is a cone, and the limit is the projection of a Gaussian onto that cone in the information metric (Andrews' boundary theory), a mixture of Gaussian and point-mass components rather than a normal law.

## Sources

- Carola Sophia Heinzel, "Consistency and central limit results for the maximum likelihood estimator in the Admixture Model", *Theor. Popul. Biol.* 166 (2025), 70-79. <https://doi.org/10.1016/j.tpb.2025.10.001>
- Preprint version (the locators in this item follow its numbering): Carola Sophia Heinzel, *Consistency and central limit results for the maximum likelihood estimator in the admixture model*, arXiv (2025). Assumption in Section 3, Theorem 2 (CLT for an open parameter space), Theorem 3 (CLT for a closed parameter space), Theorems 4 and 5 (general CLT tools). <https://doi.org/10.48550/arXiv.2507.19564>
