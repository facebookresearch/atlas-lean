# Optimal sequencing depth of one read per cell per gene

**Model.** An experiment sequences $n_{\text{cells}}$ cells at an average of $n_{\text{reads}}$ unique molecular identifiers (reads) per cell, with budget $B = n_{\text{cells}}\, n_{\text{reads}}$. For $G$ genes, the relative expression vector $X_c = (X_{c1},\dots,X_{cG})$ of cell $c$ satisfies $\sum_g X_{cg} = 1$, and

$$X_c \overset{\text{i.i.d.}}{\sim} P_X, \qquad \gamma_c \overset{\text{i.i.d.}}{\sim} P_\gamma, \qquad Y_{cg} \mid X_{cg}, \gamma_c \sim \mathrm{Poisson}(\gamma_c\, n_{\text{reads}}\, X_{cg}),$$

where $P_X$ is an unknown cell distribution (possibly a mixture of sub-populations), $\gamma_c$ is a cell size factor and $Y_{cg}$ is the observed count. Target quantities of $P_X$ are the marginal moments $M_{k,g} = \mathbb{E}[X_{cg}^k]$, the covariance matrix of $X_c$, the inactive probability $p_{0,g}(\kappa) = \mathbb{E}[e^{-\kappa X_{cg}}]$, the pairwise inactive probability $\mathbb{E}[e^{-\kappa (X_{cg_1} + X_{cg_2})}]$, and the marginal law $P_{X_g}$.

For a gene with mean relative expression $p_g = \mathbb{E}[X_{cg}]$, the expected number of reads assigned to it is $p_g B = n_{\text{reads},g}\, n_{\text{cells}}$, where $n_{\text{reads},g} = p_g\, n_{\text{reads}}$ is the mean number of reads per cell for gene $g$.

**Theorem (optimal budget allocation; stated informally in the source).** For estimating each of the quantities above, the allocation minimizing the worst-case estimation error over a broad family of distributions $P_{X_g}$ is

$$n^*_{\text{reads},g} \asymp 1, \qquad n^*_{\text{cells}} \asymp B\, p_g,$$

i.e. a sequencing depth of order one read per cell per gene, independent of the budget. The optimal error rate is attained by empirical Bayes estimators that deconvolve the Poisson noise, not by plug-in estimators computed from the normalized counts.

For a set of genes of interest whose smallest mean relative expression is $p^*$, minimizing the worst-case error over the set gives the depth $n^*_{\text{reads}} = 1/p^*$, and additional budget should be spent on more cells at that depth.

## Expansion

At fixed budget, deeper sequencing of fewer cells reduces Poisson noise per cell but leaves the cell-to-cell sampling error of $P_X$ at order $1/\sqrt{n_{\text{cells}}}$, while shallower sequencing of more cells increases the Poisson noise. Heuristically, conditional on $\gamma_c$ the $k$-th falling factorial moment of $Y_{cg}$ equals $(\gamma_c n_{\text{reads}})^k\,\mathbb{E}[X_{cg}^k]$, so moments can be estimated without bias at any depth; the Poisson part of the variance is negligible relative to cell sampling while the expected count per cell is large and dominates once it is small, so the two error sources balance at an expected count of order one per cell per gene. The same depth is optimal for the distributional quantities because their minimax rates under Poisson deconvolution are governed by the same per-cell signal-to-noise ratio. Plug-in estimates are biased at shallow depth (zero inflation inflates the apparent coefficient of variation), which is why the theorem's rate requires empirical Bayes.

## Sources

- M. J. Zhang, V. Ntranos, D. Tse, "Determining sequencing depth in a single-cell RNA-seq experiment", Nature Communications 11 (2020) 774, Results (Eq. 2 model, quantities to estimate, Theorem 1 and Eq. 3; experimental design with $n^*_{\text{reads}} = 1/p^*$), <https://doi.org/10.1038/s41467-020-14482-y>, PMCID PMC7005864.
