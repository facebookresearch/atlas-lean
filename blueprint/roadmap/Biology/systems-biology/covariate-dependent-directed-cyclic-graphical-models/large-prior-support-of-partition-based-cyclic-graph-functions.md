# Large prior support of partition-based cyclic graph functions

In the covariate-dependent cyclic structural equation model $Y = M(x) + B(x)Y + E$ with cluster-specific stable matrices, the prior makes $B(\cdot)$ piecewise constant through a random partition. Integrating over the Gaussian auxiliary model of the partition, the induced covariate-dependent weights take the form

$$\pi_j(x) = \frac{\pi_j\,N(x;\mu_j,\lambda_j)}{\sum_{j'=1}^{K^*}\pi_{j'}\,N(x;\mu_{j'},\lambda_{j'})}.$$

**Theorem (Section 4).** Let $x$ be univariate in $(a,b]$ with $-\infty < a < b < \infty$, and let every entry of $B_0(\cdot)$ (a $p\times p$ coefficient function) and $M_0(\cdot)$ (a $p$-vector) be uniformly $\nu$-Hölder continuous. Then for every $\epsilon > 0$ there is $K^* \in \mathbb{N}$ such that:

1. for any absolutely continuous priors on $(B_j,\mu_j,\lambda_j) \in \mathbb{S}_p \times \mathbb{R} \times \mathbb{R}_+$ and on $(\pi_1,\dots,\pi_{K^*})$,

$$\mathbb{P}\Big(\Big\|B_0 - \sum_{j=1}^{K^*}\pi_j(x)\,B_j\Big\|_1 < \epsilon\Big) > 0;$$

2. the same holds for $M_0$ with $(M_j,\mu_j,\lambda_j) \in \mathbb{R}^p \times \mathbb{R} \times \mathbb{R}_+$.

Here $\mathbb{S}_p$ is the set of stable matrices (spectral radius below one).

## Depends on

- [Stability of partition-averaged cyclic structural equation models](stability-of-partition-averaged-cyclic-structural-equation-models.md)

## Expansion

The theorem says that although each draw of $B(\cdot)$ is piecewise constant, partition averaging yields a kernel-mixture representation dense enough to approximate any Hölder-continuous coefficient path, so the model can represent regulatory networks that vary continuously across tissue. The proof partitions $(a,b]$ into short intervals on which Hölder continuity keeps $B_0$ nearly constant, places one narrow Gaussian kernel per interval so that the normalized weights approximate interval indicators (a Hölder-continuity lemma controls the error), and uses absolute continuity of the priors to give positive mass to a neighborhood of the matching coefficients. For the $B$ part, the target values $B_0(x)$ must themselves be stable matrices, so that the approximating $B_j$ lie in $\mathbb{S}_p$.

## Sources

- Trisha Dawn and Yang Ni, *Spatially Varying Gene Regulatory Networks via Bayesian Nonparametric Covariate-Dependent Directed Cyclic Graphical Models*, arXiv:2512.11732 (2025). <https://doi.org/10.48550/arXiv.2512.11732> Section 4 ("Large prior support", main theorem) and the Appendix (proof and Hölder-continuity lemma).
