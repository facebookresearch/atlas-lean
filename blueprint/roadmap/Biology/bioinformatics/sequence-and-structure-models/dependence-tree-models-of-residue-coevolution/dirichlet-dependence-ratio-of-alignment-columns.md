# Dirichlet-marginal dependence ratio of alignment columns

Let a multiple alignment of $n$ protein sequences have column data $D_i$ with amino-acid counts $n^i_\alpha$ ($\alpha$ over the 20 amino acids) and, for a pair of columns, joint counts $n^{ij}_{\alpha\beta}$. With a symmetric Dirichlet prior of parameter $\lambda$ on the letter distribution of a column and $\lambda'$ on the joint distribution of a pair, integrating out the unknown distributions gives

$$P(D_i) = \frac{\Gamma(20\lambda)}{\Gamma(n + 20\lambda)} \prod_{\alpha} \frac{\Gamma(n^i_\alpha + \lambda)}{\Gamma(\lambda)}, \qquad P(D_{ij}) = \frac{\Gamma(20^2 \lambda')}{\Gamma(n + 20^2 \lambda')} \prod_{\alpha\beta} \frac{\Gamma(n^{ij}_{\alpha\beta} + \lambda')}{\Gamma(\lambda')},$$

and the statistical dependence of columns $i$ and $j$ is the ratio

$$R_{ij} = \frac{P(D_{ij})}{P(D_i) P(D_j)}, \qquad \log R_{ij} = n I_{ij} + O(\log n) \quad (n \to \infty),$$

where $I_{ij}$ is the mutual information of the empirical joint distribution of the two columns. Consistency of the single-column and pair priors in a dependence-tree model requires $\lambda = 20 \lambda'$. Pairs in which either residue is a gap are excluded from the counts.

## Expansion

Each $P$ is a Dirichlet–multinomial marginal likelihood: the probability of the observed column under a letter distribution drawn from the prior. Stirling's formula turns $\log \Gamma(n p + \lambda)$ into $np \log(np) - np + O(\log n)$, and the leading terms of $\log P(D_{ij}) - \log P(D_i) - \log P(D_j)$ combine into $n \sum_{\alpha\beta} \hat p_{\alpha\beta} \log \bigl(\hat p_{\alpha\beta}/(\hat p_\alpha \hat p_\beta)\bigr) = n I_{ij}$, so $R_{ij}$ is a Bayesian, finite-sample version of $e^{n I_{ij}}$ that automatically penalizes the $20^2 - 1$ free parameters of a joint distribution. The constraint $\lambda = 20\lambda'$ makes the marginal of the pair prior on one column equal to the single-column prior. Treating gaps as a 21st letter creates spurious dependence between columns that are close in sequence, because gaps occur in blocks.

## Sources

- Burger L, van Nimwegen E. Disentangling direct from indirect co-evolution of residues in protein alignments. *PLoS Computational Biology* (2010), Materials and Methods, "Probabilistic model", "Calculating posteriors" and "Phylogenetic correction", equations (2)–(15) and (27). DOI <https://doi.org/10.1371/journal.pcbi.1000633>. PMCID PMC2793430.
