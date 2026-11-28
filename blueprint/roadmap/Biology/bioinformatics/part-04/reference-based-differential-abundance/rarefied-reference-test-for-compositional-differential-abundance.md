# Rarefied reference test for compositional differential abundance

**Setting.** Each sample has a latent composition $\mathbf P$ over $m$ taxa (microbial relative abundances), a group label or trait $\mathbf Y$, and observed counts $\mathbf X\mid N,\mathbf P\sim\mathrm{Multinom}(N,\mathbf P)$ with sequencing depth $N$. For an indicator vector $\mathbf b$ of a set of taxa, write $\mathbf b'\mathbf P$ for their total abundance and $\mathbf P(\mathbf b)$ for the vector of their abundances.

**Definition (reference set).** A set of taxa $\{b_1,\dots,b_r\}$ is a *reference set* if $\mathbf b'\mathbf P>0$ almost surely and

$$
\frac{\mathbf P(\mathbf b)}{\mathbf b'\mathbf P}\ \perp\!\!\!\perp\ \mathbf Y,
$$

i.e. the within-reference composition does not depend on the trait. Taxon $j$ is tested by the null hypothesis that $\mathbf P(\mathbf e_j)/\mathbf b_j'\mathbf P$, its abundance relative to the reference set augmented by taxon $j$, is independent of $\mathbf Y$.

**Test (rarefied reference).** For each sample, subsample without replacement the counts of the reference taxa plus taxon $j$ down to a common total $\lambda$ (the minimum over samples), and apply any valid two-sample or independence test to the subsampled counts of taxon $j$ against $\mathbf Y$.

**Lemma (rarefaction yields a binomial).** If $(U,V,W)\sim\mathrm{Multinom}(N,(P_U,P_V,1-P_U-P_V))$ and $\tilde U\mid U,V\sim\mathrm{Hypergeom}(\lambda,U,U+V)$, then

$$
\tilde U\mid\lambda,P_U,P_V,U+V\ \sim\ \mathrm{Bin}\Big(\lambda,\frac{P_U}{P_U+P_V}\Big).
$$

**Proposition (validity).** Under the null hypothesis for taxon $j$, the rarefied test has level $\alpha$.

**Proposition (normalized counts are biased).** Without rarefaction,

$$
\mathbb E\Big\{\frac{\mathbf X(\mathbf e_j)}{\max(1,\mathbf b_j'\mathbf X)}\ \Big|\ \mathbf P\Big\}=\frac{\mathbf P(\mathbf e_j)}{\mathbf b_j'\mathbf P}\ \mathbb P(\mathbf b_j'\mathbf X>0\mid\mathbf P),
$$

so naive ratio normalization mixes the target ratio with a depth-dependent detection probability.

## Expansion

Conditioning on the reference-plus-$j$ total turns multinomial counts into a binomial with success probability equal to the within-reference proportion; rarefying to a common $\lambda$ removes the dependence on the sample-specific total, which may differ systematically between groups. Under the null that proportion is independent of $\mathbf Y$, so the rarefied counts are exchangeable across groups and any permutation or rank test is exact. The bias identity shows why dividing by reference totals is not enough: the factor $\mathbb P(\mathbf b_j'\mathbf X>0\mid\mathbf P)$ varies with depth and composition, inflating type I error when depths differ by group. The method requires choosing a reference set of taxa believed not to change, which the source selects by a data-driven variance criterion.

## Sources

- Barak Brill, Amnon Amir, Ruth Heller, "Testing for differential abundance in compositional counts data, with application to microbiome studies", arXiv:1904.08937: Section 2: Definition 2.1 (reference set); Section 3: Propositions 1 and 2; Appendix A: Lemma 1. <https://doi.org/10.48550/arXiv.1904.08937>
