# Locus-averaged $F_{ST}$ as the spectrum of the between-population genotype matrix

**Setting.** A haploid sample of $n$ individuals is genotyped at $L$ biallelic loci, $x_{i\ell} \in \{0,1\}$ counting derived alleles (diploids are treated as two haploids). Each individual belongs to one of $K \ge 2$ predefined populations; population $k$ has sample fraction $c_k = n_k/n$ and derived-allele frequency $p_{k\ell}$ at locus $\ell$, and $P_\ell = \sum_k c_k p_{k\ell}$ is the pooled frequency. At each locus set

$$H_S = 2\sum_{k=1}^K c_k p_k(1-p_k), \qquad H_T = 2P(1-P), \qquad D_{ST} = H_T - H_S, \qquad F_{ST} = D_{ST}/H_T,$$

and write $E[Q] = \frac1L\sum_{\ell=1}^L Q_\ell$ for the average over loci.

**Decomposition.** The column-centered matrix $Z$ has entries $z_{i\ell} = x_{i\ell} - P_\ell$. For $i$ in population $k$ write $z_{i\ell} = z^{ST}_{i\ell} + z^{S}_{i\ell}$ with

$$z^{ST}_{i\ell} = p_{k\ell} - P_\ell = \sum_{j \ne k} c_j (p_{k\ell} - p_{j\ell}), \qquad z^{S}_{i\ell} = x_{i\ell} - p_{k\ell}.$$

$Z^{ST}$ (between-population matrix) has rank at most $K-1$; $Z^{S}$ is the within-population matrix. The scaled versions $Z^{sc}, Z^{ST,sc}, Z^{S,sc}$ divide column $\ell$ by $\sqrt{P_\ell(1-P_\ell)}$. Let $\sigma_k^2(\cdot)$ and $\rho_k^2(\cdot)$ denote the eigenvalues of $MM^{\top}/n$ (squared singular values divided by $n$) for an unscaled or scaled matrix $M$, in decreasing order.

**Theorem 1.** For $K \ge 2$,

$$E[F_{ST}] = \frac1L\sum_{k=1}^{K-1} \rho_k^2(Z^{ST,sc}), \qquad \frac{E[D_{ST}]}{2} = \frac1L\sum_{k=1}^{K-1} \sigma_k^2(Z^{ST}).$$

**Corollary (within-population form).** Because $\|Z\|^2 = \|Z^{ST}\|^2 + \|Z^{S}\|^2$ (Hilbert–Schmidt norms),

$$E[F_{ST}] = 1 - \frac1L\sum_{j=1}^{n-K}\rho_j^2(Z^{S,sc}), \qquad E[D_{ST}] = E[H_T] - \frac2L\sum_{j=1}^{n-K}\sigma_j^2(Z^{S}).$$

**PCA approximation.** If the separation condition $\sigma_{K-1}^2(Z^{ST}) > \sigma_1^2(Z^{S})$ holds and the residual spectrum follows random-matrix (Marchenko–Pastur) scaling with $L/n$ fixed, then the leading $K-1$ PCA eigenvalues satisfy $|\sigma_k^2(Z)/L - \sigma_k^2(Z^{ST})/L| = O(1/L)$, so $E[F_{ST}] \approx \frac1L\sum_{k<K}\rho_k^2(Z^{sc})$ with error $O(K/L)$.

## Depends on

- [Column-centred genotype matrix](../../coalescence-times-f-statistics-and-pca/centered.md)

## Proof depends on

- [Real singular value decomposition](../../../../LinearAlgebra/matrix-decompositions/singular-value-decomposition/singular-value-decomposition-theorem/real-singular-value-decomposition.md)

## Expansion

At one locus the between-population column takes the value $p_k - P$ on the $n c_k$ rows of population $k$, so its squared norm is $n\sum_k c_k (p_k-P)^2$. Expanding $H_T - H_S = 2(\sum_k c_k p_k^2 - P^2) = 2\sum_k c_k (p_k - P)^2$ shows this equals $n D_{ST}/2$; dividing the column by $\sqrt{P(1-P)}$ turns it into $n D_{ST}/(2P(1-P)) = n F_{ST}$. Summing over loci, $\|Z^{ST}\|^2 = nL\,E[D_{ST}]/2$ and $\|Z^{ST,sc}\|^2 = nL\,E[F_{ST}]$, while the squared Hilbert–Schmidt norm is the sum of squared singular values, of which at most $K-1$ are non-zero. The within-population columns have zero mean inside each population, so they are orthogonal to the population-constant between-population columns, giving the Pythagorean identity and the corollary. The theorem supports defining multilocus $F_{ST}$ as an average of ratios, and it extends verbatim to adjusted genotype matrices (e.g. residuals of a latent factor regression on environmental covariates), giving an $F_{ST}$-like statistic equal to the average $R^2$ of regressing scaled surrogate genotypes on population labels.

## Sources

- O. François, C. Gain, "A spectral theory for Wright's inbreeding coefficients and related quantities", PLoS Genetics (2021), Theorem 1, Corollary, Eqs. (1)–(7) and Methods, <https://doi.org/10.1371/journal.pgen.1009665>, PMCID PMC8320931.
