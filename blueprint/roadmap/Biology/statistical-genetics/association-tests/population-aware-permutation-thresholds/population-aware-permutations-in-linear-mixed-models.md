# Population-aware permutations in linear mixed models

**Model.** For $n$ phenotypes $y\in\mathbb{R}^n$ and a fixed-effects matrix $X\in\mathbb{R}^{n\times c}$ (intercept, covariates and the SNP under test), the linear mixed model is

$$y = X\beta + u + \epsilon,\qquad u\sim N(0,\sigma_g^2 K),\qquad \epsilon\sim N(0,\sigma_e^2 I),$$

so $y\sim N(X\beta, V)$ with $V = \sigma_g^2K + \sigma_e^2I$ and $K$ a genetic similarity matrix.

**Lemma.** Let $\tau$ be a permutation of $\{1,\dots,n\}$ with permutation matrix $P_\tau$. Permuting the entries of $y$ and the rows and columns of $V$ by $\tau$ (that is, $y\mapsto P_\tau y$, $V\mapsto P_\tau VP_\tau^{\top}$) is equivalent to permuting the rows of $X$ by $\tau^{-1}$ ($X\mapsto P_\tau^{\top}X$) and leaving $y$ and $V$ unchanged: the likelihoods, the generalized least-squares estimates of $\beta$ and the test statistics coincide.

**Consequence.** Permuting only $y$ breaks both the genotype-phenotype link and the relatedness encoded in $V$. Permuting $y$ together with $V$ preserves the population structure, and by the lemma this "population-aware" permutation can be carried out by permuting the rows of each SNP's fixed-effects matrix. The covariate block is shared by all SNPs, since for $X = [Z, s]$ and symmetric $A$,

$$X^{\top}AX = \begin{pmatrix} Z^{\top}AZ & Z^{\top}As\\ (Z^{\top}As)^{\top} & s^{\top}As\end{pmatrix},$$

so $Z^{\top}AZ$ is computed once per permutation and only the SNP-dependent blocks are computed in batches.

## Depends on

- [Variance components of the linear mixed model](../../bolt-lmm-mixed-model-association/model.md)
- [Generalized least-squares estimator](../../bolt-lmm-mixed-model-association/gls.md)

## Expansion

With $V' = P_\tau VP_\tau^{\top}$, $V'^{-1} = P_\tau V^{-1}P_\tau^{\top}$ and $P_\tau^{\top}P_\tau = I$, the Gaussian log-likelihood satisfies $\log N(P_\tau y\mid X\beta, V') = \log N(y\mid P_\tau^{\top}X\beta, V)$, since the quadratic form $(P_\tau y - X\beta)^{\top}V'^{-1}(P_\tau y - X\beta) = (y - P_\tau^{\top}X\beta)^{\top}V^{-1}(y - P_\tau^{\top}X\beta)$ and $\det V' = \det V$. The variance-component ratio and the eigen-rotated design still have to be recomputed for each permutation, but the block decomposition makes population-aware permutations about as fast as phenotype-only permutations. In simulations on skewed phenotypes, thresholds from population-aware permutations were slightly stricter and gave a lower phenotype-wise false discovery rate than phenotype-only permutations, Bonferroni or Benjamini-Hochberg.

## Sources

- John M, Korte A, Todesco M, Grimm DG. Population-aware permutation-based significance thresholds for genome-wide association studies. *Bioinformatics Advances* 4(1):vbae168 (2024), Section 2, Eq. 1, Lemma 1 and Lemma 2. <https://doi.org/10.1093/bioadv/vbae168>. PMCID: PMC11639184.
