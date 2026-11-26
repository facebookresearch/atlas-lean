# Epitope grouping by escape-profile dissimilarity

Let $A \in \mathbb{R}_{\ge 0}^{N \times M}$ be the matrix whose entry $A_{nm}$ is the total escape score of antibody $n$ at antigen site $m$, restricted to the $M$ *informative sites*: sites escaped by at least six antibodies (each with site escape score greater than $1$, per the source's "Antibody clustering" criterion, distinct from the per-antibody noise filter). Writing $A_n$ for row $n$ and $x_n = A_n - \overline{A_n}\mathbf{1}$ for its centred version, the dissimilarity between antibodies is

$$D_{ij} = 1 - \operatorname{corr}(A_i, A_j), \qquad \operatorname{corr}(A_i,A_j) = \frac{\langle x_i, x_j \rangle}{\lVert x_i\rVert\,\lVert x_j\rVert} \in [-1,1],$$

so $D_{ij} \in [0,2]$, $D_{ii} = 0$, and $D$ is symmetric. Classical multidimensional scaling of $D$ embeds the antibodies in $\mathbb{R}^k$ for a small $k$, and $k$-medoids clustering of the embedded points partitions the antibodies into epitope groups: classes whose members are escaped by mutations at overlapping sets of sites.

## Depends on

- [Escape score of a variant in a selection experiment](escape-score-of-a-variant.md)

## Expansion

Correlation rather than Euclidean distance is the right comparison because antibodies differ by orders of magnitude in overall escape magnitude while the question is which sites matter; centring and normalizing each profile removes that nuisance scale, so two antibodies escaped by the same residues are close even when one is far more sensitive. Restricting to informative sites removes columns that carry only noise, which would otherwise dilute the correlation toward zero uniformly. Classical scaling is applied because $1 - \operatorname{corr}$ is not a Euclidean distance; the embedding yields coordinates in which a centroid-free method such as $k$-medoids, which picks actual antibodies as cluster representatives, is stable against the outlying profiles that single highly specific antibodies produce. The resulting groups are a structural hypothesis: antibodies in one group compete for an overlapping footprint, so a single antigenic mutation can defeat them together.

## Sources

- Cao Y, Wang J, Jian F, et al. Omicron escapes the majority of existing SARS-CoV-2 neutralizing antibodies. *Nature* 602:657-663 (2022), Methods, "Antibody clustering". DOI <https://doi.org/10.1038/s41586-021-04385-3>. PMCID PMC8866119.
