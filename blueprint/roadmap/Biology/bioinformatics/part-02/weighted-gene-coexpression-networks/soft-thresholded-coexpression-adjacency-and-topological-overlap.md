# Soft-thresholded coexpression adjacency and topological overlap

**Setting.** Let $x_1, \dots, x_p \in \mathbb R^n$ be expression profiles of $p$ genes over $n$ samples (normalized, log-transformed and filtered for variability), and let $\mathrm{cor}$ denote Pearson correlation.

- The **unsigned soft-thresholded adjacency** with power $\beta \ge 1$ is

$$a_{ij} = |\mathrm{cor}(x_i, x_j)|^{\beta} \in [0,1] \quad (i \neq j), \qquad a_{ii} = 0 .$$

- The **connectivity** of gene $i$ is $k_i = \sum_{u} a_{iu}$.
- The **topological overlap** of genes $i \neq j$ is

$$\omega_{ij} = \frac{l_{ij} + a_{ij}}{\min(k_i, k_j) + 1 - a_{ij}}, \qquad l_{ij} = \sum_{u \neq i, j} a_{iu}a_{uj},$$

and $1 - \omega_{ij}$ is the topological-overlap dissimilarity, which is clustered hierarchically; modules are branches of the dendrogram cut by a dynamic tree-cut procedure.

**Proposition.** For every $i \neq j$, $0 \le \omega_{ij} \le 1$; $\omega_{ij} = 0$ if and only if $a_{ij} = 0$ and $i, j$ share no neighbor of positive weight.

**Effect of the power.** Since $a_{ij}/a_{i'j'} = (|\mathrm{cor}_{ij}|/|\mathrm{cor}_{i'j'}|)^{\beta}$, raising $\beta$ suppresses weak correlations relative to strong ones without discarding them (a soft rather than hard threshold). Larger $\beta$ leaves fewer genes with strong adjacencies and so assigns fewer genes to fewer modules; smaller $\beta$ yields more and larger modules with less coherent expression within modules. A common choice of $\beta$ is the smallest power at which the connectivity distribution approximately follows a power law (scale-free topology fit). Unsigned correlations place positively and negatively correlated genes in the same module.

## Expansion

Because each $a_{uj} \le 1$, $l_{ij} \le \sum_{u \neq i,j}a_{iu} = k_i - a_{ij}$ and likewise $l_{ij} \le k_j - a_{ij}$, so the numerator is at most $\min(k_i, k_j)$; the denominator is at least $\min(k_i,k_j)$ because $a_{ij} \le 1$, and it is positive. Hence $\omega_{ij} \le 1$, and nonnegativity is clear. The overlap rewards pairs that are both directly correlated and correlated with the same other genes, which makes module detection less sensitive to noise in individual correlations. In condition-dependent analyses (separate data sets per experiment), modules capture tissue- or treatment-specific coexpression that is diluted in a single condition-independent compendium.

## Sources

- K. L. Childs, R. M. Davidson, C. R. Buell, "Gene coexpression network analysis as a source of functional annotation for rice genes", PLoS One (2011), Methods (WGCNA procedure: unsigned correlation, soft-thresholding power, topological overlap, dynamic tree cut, choice of the power) and Discussion, <https://doi.org/10.1371/journal.pone.0022196>, PMCID PMC3142134.
- B. Zhang, S. Horvath, "A general framework for weighted gene co-expression network analysis", Statistical Applications in Genetics and Molecular Biology (2005), <https://doi.org/10.2202/1544-6115.1128>.
