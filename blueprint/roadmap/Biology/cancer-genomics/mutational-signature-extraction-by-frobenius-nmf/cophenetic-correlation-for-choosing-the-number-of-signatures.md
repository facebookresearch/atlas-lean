# Cophenetic correlation for choosing the number of signatures

Fix a rank $k$ and run a non-negative factorization $R$ times from random initializations. For each run $r$ assign every sample to the component of largest exposure, and let the connectivity matrix be $C^{(r)}_{mm'} = \mathbf{1}\{m, m' \text{ assigned to the same component in run } r\}$. The consensus matrix is $\bar{C} = R^{-1}\sum_{r=1}^{R} C^{(r)} \in [0,1]^{M \times M}$, and $1 - \bar{C}$ is used as a dissimilarity for average-linkage hierarchical clustering, which induces cophenetic distances $d_{mm'}$ (the merge height at which $m$ and $m'$ first join). The cophenetic correlation coefficient at rank $k$ is the Pearson correlation

$$\rho(k) = \operatorname{corr}\big( \{1 - \bar{C}_{mm'}\}_{m < m'},\ \{d_{mm'}\}_{m<m'} \big) \in [-1,1],$$

defined when neither vector of pairwise values is constant. At rank $k = 1$ every sample is assigned to the single component in every run, so $\bar C$ has all entries $1$, both vectors are constant and $\rho(1)$ is undefined; the same happens at any rank whose runs all agree on one partition with a single cluster.

Ranks are compared by $\rho(k)$ together with the average reconstruction error $\lVert A - W H\rVert_F$; a rank is retained while $\rho(k)$ stays high and the error curve still falls steeply, and the chosen $k$ is the largest such rank.

## Depends on

- [Frobenius-norm non-negative factorization of a mutation catalogue](frobenius-nmf-model-of-a-mutation-catalogue.md)
- [States reachable by UPGMA](../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/upgma-reaches.md)

## Remarks

If a rank captures real structure, independent runs converge to the same partition of samples, every entry of $\bar{C}$ is near $0$ or $1$, and the consensus dissimilarity is already ultrametric, so the hierarchical clustering reproduces it exactly and $\rho(k) \approx 1$. When the rank exceeds the number of reproducible components, runs split samples differently, intermediate entries appear in $\bar{C}$, and the cophenetic correlation drops. The criterion therefore measures stability, not fit: reconstruction error decreases with $k$ by construction, so it can only be read through the slope of its decline, and the two diagnostics are used together.

## Sources

- Nik-Zainal S, Alexandrov LB, Wedge DC, et al. Mutational processes molding the genomes of 21 breast cancers. *Cell* 149:979-993 (2012), Extended Experimental Procedures and Figure S2. DOI <https://doi.org/10.1016/j.cell.2012.04.024>. PMCID PMC3414841.
- Brunet JP, Tamayo P, Golub TR, Mesirov JP. Metagenes and molecular pattern discovery using matrix factorization. *PNAS* 101:4164-4169 (2004). DOI <https://doi.org/10.1073/pnas.0308531101>.
