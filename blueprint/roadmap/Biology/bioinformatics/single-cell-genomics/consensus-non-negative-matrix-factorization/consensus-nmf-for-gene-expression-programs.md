# Consensus NMF for gene expression programs

Let $\tilde C \in \mathbb{R}_{\ge 0}^{N \times H}$ be a normalized expression matrix ($N$ cells, $H$ over-dispersed genes), modelled as $\tilde C \approx U G$ with non-negative usages $U \in \mathbb{R}_{\ge 0}^{N \times K}$ and gene expression programs $G \in \mathbb{R}_{\ge 0}^{K \times H}$. Consensus NMF (cNMF) proceeds as follows.

1. Run NMF $R$ times with random seeds, $U^{(r)} G^{(r)} \approx \tilde C$, normalize every program row to unit $\ell_2$ norm and stack them into an $RK \times H$ matrix $\mathbf{G}$.
2. With $L = \rho R$ for a fraction $\rho \in (0, 1]$, keep the rows $G_l$ whose mean distance to their $L$ nearest rows, $D(G_l, L) = \frac{1}{L} \sum_{G_n \in N_L(G_l)} \lVert G_l - G_n \rVert_2$, is below a threshold $\tau$.
3. Cluster the kept rows by $k$-means into $K$ clusters $A_1, \dots, A_K$ and set the consensus program to the gene-wise median $G^{(c)}_{kj} = \operatorname{median}\{G_{lj} : l \in A_k\}$, then normalize each consensus program to unit $\ell_1$ norm, giving $\tilde G^{(c)}$.
4. Fit usages by non-negative least squares, $\min_{U_{i1}, \dots, U_{iK} \ge 0} \lVert \tilde C_i - \sum_k U_{ik} \tilde G^{(c)}_k \rVert^2$ for each cell $i$, and normalize each cell's usages to sum to $1$.
5. With these usages fixed, refit each program in transcripts per million over all genes by non-negative least squares per gene.

$K$ is chosen by inspecting solution stability (silhouette score of the replicate programs) against the Frobenius reconstruction error as functions of $K$.

## Depends on

- [Reconstruction matrix in nonnegative matrix factorization](../../../cancer-genomics/mutational-signatures-and-bayesian-nmf/recon.md)

## Expansion

NMF is non-convex, so different initializations converge to different local optima; programs that recur across replicates form tight clusters in the stacked matrix, while idiosyncratic ones are isolated and removed by the nearest-neighbour filter, where $\rho$ is roughly the fraction of replicates in which a program must appear. The gene-wise median is robust to residual outliers, and with programs fixed each usage fit is a convex quadratic program. Because NMF components are additive and non-negative, a cell can use an identity program (its cell type) and activity programs (cell cycle, hypoxia, stimulus responses) simultaneously, which hard clustering cannot represent; in simulations NMF, ICA and LDA recovered such programs whereas principal components were mixtures of them. The procedure adapts the consensus approach used for mutational signature extraction.

## Sources

- D. Kotliar, A. Veres, M. A. Nagy et al., "Identifying gene expression programs of cell-type identity and cellular activity with single-cell RNA-Seq", eLife 8 (2019), e43803, <https://doi.org/10.7554/eLife.43803> (PMC6639075). Materials and methods, consensus non-negative matrix factorization and choice of the number of components.
