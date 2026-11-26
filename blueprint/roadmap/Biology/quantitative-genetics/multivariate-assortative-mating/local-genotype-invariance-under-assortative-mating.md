# Local genotype invariance under assortative mating

**Model.** An outbreeding population descends from a randomly mating founder generation at Hardy-Weinberg equilibrium. Individuals carry $m$ autosomal biallelic loci $\mathbf G \in \Omega_m = \{0,1,2\}^m$ and express $p$ traits

$$\mathbf X = \mathbf G\Lambda + \mathbf E, \qquad \mathbf E \sim N(\mathbf 0, \Sigma_E),$$

with $\Sigma_E$ positive definite and an effect matrix $\Lambda \in \mathbb R^{m\times p}$ whose entries are $O(m^{-1/2})$ (each locus contributes variance of order $1/m$), each trait having $O(m)$ causal loci; trait values are restricted to a compact high-probability region $\mathcal X$. Assortment is primary phenotypic: given a mate cross-correlation matrix $R_{\sigma\times\varphi} \in [-1,1]^{p\times p}$ and cross-covariance $\Sigma_{\sigma\times\varphi} = \Sigma_X^{1/2} R_{\sigma\times\varphi}\Sigma_X^{1/2}$, the mate of an individual with traits $\mathbf X_\sigma$ has

$$\mathbf X_\varphi = \Sigma_{\sigma\times\varphi}\Sigma_X^{-1}\mathbf X_\sigma + \boldsymbol\varepsilon_\varphi, \qquad \boldsymbol\varepsilon_\varphi \sim N\big(\mathbf 0, \Sigma_X - \Sigma_{\sigma\times\varphi}^{\top}\Sigma_X^{-1}\Sigma_{\sigma\times\varphi}\big),$$

and spousal genotypes are independent given the phenotypes. A collection $\mathcal G^s$ of loci is *atomic* if $|\mathcal G^s| = O(1)$ as $m \to \infty$.

**Lemma A.2.** For an atomic segment, every configuration $\mathbf g^s$ and every $\mathbf x \in \mathcal X$,

$$\Pr(\mathbf G^s = \mathbf g^s \mid \mathbf X = \mathbf x) = \big(1 + O(m^{-1/2})\big)\Pr(\mathbf G^s = \mathbf g^s).$$

**Theorem A.1 (assortment invariance).** Let $\mu_s^{(t)}$ be the law of the genotypes of an atomic segment in generation $t$, with $\mu_s^{(0)}$ the random-mating (Hardy-Weinberg) law. For $t = o(m^{1/2})$ and every $\mathbf g^s$,

$$\mu_s^{(t)}(\mathbf g^s) = \big(1 + O(m^{-1/2})\big)\mu_s^{(0)}(\mathbf g^s).$$

**Corollary A.1.** For any measurable $h$ of an atomic segment and every $k \in \mathbb N$, $\mathbb E_{\mu_s^{(t)}}[h(\mathbf G^s)^k] = (1 + O(m^{-1/2}))\,\mathbb E_{\mu_s^{(0)}}[h(\mathbf G^s)^k]$.

Consequently, taking $m \to \infty$ before any limit in $t$, single-locus variances stay at $2f(1-f)$ for allele frequency $f$, and the segregation (Mendelian sampling) covariance matrix stays at $\Sigma_S = \tfrac12\Sigma_G^{(0)}$ in every generation: assortment builds up covariance only between many loci jointly, not within any bounded set of them.

## Expansion

Conditioning on the trait vector changes the weight of a configuration of a bounded set of loci only through the Gaussian density of $\mathbf x - \mathbf g^s\Lambda$ against the remaining polygenic background; since $\mathbf g^s\Lambda$ shifts the mean by $O(m^{-1/2})$ and $\mathbf x$ lies in a compact set, the ratio of densities for two configurations is $1 + O(m^{-1/2})$ (Lemma A.1), which gives Lemma A.2 by Bayes' rule. Offspring segment laws are obtained from parental laws by Mendelian transmission, and parents are selected by phenotype only, so each generation multiplies the error by at most $1 + O(m^{-1/2})$; over $t = o(m^{1/2})$ generations the accumulated factor is still $1 + o(1)$. This is the multivariate, phenotype-based counterpart of the fact that the infinitesimal model's segregation variance does not depend on the pedigree's selection or mating history.

## Depends on

- [The infinitesimal model of inheritance](../mendelian-segregation-and-the-infinitesimal-mode/infinitesimal-model-definition.md)
- [Complete positive assortative mating with equal genotype-class contribution](../../population-genetics/hardy-weinberg-law/complete-positive-assortative-mating-by-genotype.md)

## Sources

- K. Hlynsson, "A high-dimensional perspective of assortative mating: definition, dynamics, and limiting results" (2026), Section 2.1 (model of genotype, phenotype and assortment), Section 3.2 (invariants under assortment), Appendix A (Lemmas A.1 and A.2, Theorem A.1, Corollary A.1), <https://doi.org/10.48550/arXiv.2611.29703>.
