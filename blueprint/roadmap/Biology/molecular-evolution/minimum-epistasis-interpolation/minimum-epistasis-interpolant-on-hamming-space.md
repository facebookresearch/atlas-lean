# Minimum epistasis interpolant on Hamming space

**Setting.** Sequence space is the Hamming graph on $\alpha^l$ genotypes (length $l$, alphabet size $\alpha$), with genotypes adjacent when they differ at one site, and $f$ a phenotype observed on a subset $B$ of genotypes. A **face** is a quadruple consisting of a genotype, two single mutants at different sites, and the corresponding double mutant; for a face written $(ab, Ab, aB, AB)$ the local epistatic coefficient is

$$\epsilon = (f_{AB} - f_{aB}) - (f_{Ab} - f_{ab}),$$

the change in the effect of $a \to A$ between backgrounds $b$ and $B$. Its square $\epsilon^2$ does not depend on the choice of reference genotype. The **minimum epistasis interpolant** $\hat f$ agrees with $f$ on $B$ and minimizes the average of $\epsilon^2$ over all faces.

**Linear system.** With $c(i,j)$ the coefficients of the quadratic form $\sum_{\text{faces}} \epsilon^2$, the interpolant solves the $\alpha^l - |B|$ equations

$$\sum_{j \notin B} c(i,j)\,\hat f(j) = -\sum_{j \in B} c(i,j)\, f(j), \qquad i \notin B,$$

which have a unique solution if and only if the least-squares fit of the additive (non-epistatic) model to the observed genotypes is unique.

**Properties.**
1. (Local average.) Each genotype lies in $\binom l2 (\alpha-1)^2$ faces, each of whose other three members gives an additive prediction for it; for every unobserved $i$, $\hat f(i)$ equals the mean of these predictions.
2. (Distance-shell form.) With $d_k(i)$ the mean of $\hat f$ over genotypes at Hamming distance $k$ from $i$,

$$\hat f(i) = d_1(i) + \big(d_1(i) - d_2(i)\big).$$

3. (Biharmonic form.) If $L$ is the graph Laplacian of the Hamming graph, the constrained minimization is the boundary-value problem $(L^2 - \alpha L)\hat f = 0$ off $B$ with $\hat f = f$ on $B$, a discrete analogue of the biharmonic equation solved by thin-plate splines.
4. (Noise.) Predictions are linear in the observed values, so their noise-induced variance is explicit; in the data-dense regime the distance-shell form gives roughly an $l(\alpha-1)/5$-fold reduction of prediction variance relative to measurement noise.

## Depends on

- [Reciprocal sign epistasis, multiple peaks and the small-face limitation](../../population-genetics/selection-migration-and-transmission/fitness-landscapes/epistasis-and-landscape-structure.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

For two biallelic loci the double mutant is fixed by setting $\epsilon = 0$, the additive prediction; in general one cannot zero every face at once, and minimizing the total $\epsilon^2$ spreads the unavoidable epistasis as evenly as possible. The stationarity condition at a free genotype says it equals the average of what its faces predict, which is property 1, and averaging those predictions by distance class gives the Taylor-like correction in property 2: nearest neighbours, corrected by how phenotype changes one step further out. Since $\epsilon$ is a discrete second difference, summing $\epsilon^2$ is a discrete integrated squared curvature, which explains the squared-Laplacian operator. Iteratively replacing unobserved values by their local non-epistatic prediction converges to the same solution. Unlike low-order regression, the interpolant leaves observed data untouched and accommodates higher-order epistasis while adding little spurious structure, such as false local fitness maxima.

## Sources

- J. Zhou, D. M. McCandlish, "Minimum epistasis interpolation for sequence-function relationships", Nature Communications 11:1782 (2020), Eqs 1, 3 and 5 and the properties section (Supplementary Methods Propositions 1–3), <https://doi.org/10.1038/s41467-020-15512-5>, PMCID PMC7156698.
