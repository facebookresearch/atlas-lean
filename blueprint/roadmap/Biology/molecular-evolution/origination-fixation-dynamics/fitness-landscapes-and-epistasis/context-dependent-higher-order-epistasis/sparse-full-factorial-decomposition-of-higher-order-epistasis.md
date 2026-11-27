# Sparse full-factorial decomposition of higher-order epistasis

Let $L$ binary mutations be indexed by $[L]=\{1,\dots,L\}$, and let a genotype be identified with the set $S\subseteq[L]$ of mutations it carries, $\varnothing$ being the ancestor. Code genotype $S$ by indicators $x_k=\mathbf 1[k\in S]$ and consider the saturated model

$$m_S=\sum_{T\subseteq S}\beta_T,\qquad\text{equivalently}\qquad y=\sum_{T\subseteq[L]}\beta_T\prod_{k\in T}x_k+\varepsilon,$$

where $m_S$ is the mean phenotype of genotype $S$. Then:

1. **Möbius inversion.** The coefficients are determined by the $2^L$ means,

$$\beta_T=\sum_{S\subseteq T}(-1)^{|T|-|S|}\,m_S,$$

and least squares on replicated data recovers them with each $m_S$ replaced by the cell sample mean. The order of $\beta_T$ is $|T|$; for $|T|=2$ it is the interaction contrast $m_{\{k,l\}}-m_{\{k\}}-m_{\{l\}}+m_\varnothing$.
2. **Contexts as factors.** Adding categorical background factors with $a_1,\dots,a_r$ levels and all their interactions with the mutations gives a saturated model with $2^L\prod_t a_t$ coefficients, one per genotype-by-context cell. For three mutations, three species backgrounds of the enzyme and three protein-quality-control backgrounds this is $2^3\cdot3\cdot3=72$.
3. **Sparse estimation.** Because the saturated model interpolates the cell means, interactions are selected by penalized regression on standardized phenotypes,

$$\hat\beta=\arg\min_\beta\ \frac{1}{2N}\|y-X\beta\|_2^2+\lambda\Bigl[\alpha\|\beta\|_1+\tfrac{1-\alpha}{2}\|\beta\|_2^2\Bigr],$$

with $\alpha=1$ (the lasso) and $\lambda$ the largest value within one cross-validated standard error of the minimum. A coefficient set to zero is read as an absent interaction of that order.

## Depends on

- [Reciprocal sign epistasis, multiple peaks and the small-face limitation](../../../../population-genetics/selection-migration-and-transmission/fitness-landscapes/epistasis-and-landscape-structure.md)
- [Lasso objective](../../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/lasso.md)

## Proof depends on

- [Möbius inversion formula](../../../../../Order/ordered-sets/incidence-algebras-and-the-m-bius-function/moebius-inversion-iff.md)
- [Closed-form solution of the normal equations](../../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/normal-inv.md)

## Expansion

Item 1 is Möbius inversion on the Boolean lattice: $m_S=\sum_{T\subseteq S}\beta_T$ is the zeta transform, and the alternating sum is its inverse; with one column per cell the design matrix is square and invertible, so least squares fits every cell mean exactly. The coefficients depend on the coding: with $0/1$ indicators they are effects relative to the ancestor, while $\pm1$ coding gives Walsh (Fourier) coefficients that average over backgrounds, so orders and signs reported under one coding do not transfer to the other. Fitting the within-context model separately in each background, as the source does with phenotypes normalized within each species-by-environment group, shows directly how the same mutation set has different interaction coefficients in different environments. In the source's data on trimethoprim resistance and protein abundance of dihydrofolate reductase, interactions in total contributed more to IC50 than main effects, and the largest single coefficient for abundance was third order.

The lasso's selection is a modeling choice, not a test: nonzero coefficients carry no error control, and correlated columns can trade off. The derivation of item 1 and the coding remark are supplied here; the source reports the fitted coefficients and the model specification.

## Sources

- R. F. Guerrero, S. V. Scarpino, J. V. Rodrigues, D. L. Hartl and C. B. Ogbunugafor, "Proteostasis environment shapes higher-order epistasis operating on antibiotic resistance", Genetics 212 (2019), 565–575, Materials and Methods ("Statistical analysis": initial generalized linear models and "Regularized regressions") and Results ("Decomposition of epistasis for IC50", "Decomposition of epistasis for protein abundance", "Epistatic effects of SNPs across PQC contexts"), <https://doi.org/10.1534/genetics.119.302138> (PMC6553834).
