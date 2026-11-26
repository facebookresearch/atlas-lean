# FarmCPU: alternating fixed- and random-effect models for association testing

Let $y_i$ be the phenotype and $S_{ij}$ the genotype at marker $j$ of individual $i$, for $n$ individuals and $m$ markers. FarmCPU (fixed and random model circulating probability unification) maintains a set of $t$ **pseudo QTNs** (markers treated as putative causal variants) with genotypes $M_{i1}, \dots, M_{it}$ and alternates two models.

**Fixed-effect model (FEM).** Each marker $j$ not in the pseudo-QTN set is tested, one at a time, in

$$y_i = M_{i1}b_1 + \dots + M_{it}b_t + S_{ij}d_j + e_i, \qquad \mathbb{E}e_i = 0,\ \operatorname{Var}e_i = \sigma_e^2,$$

by the $P$ value of $d_j$. Each pseudo QTN receives, by **substitution**, the most significant $P$ value its own coefficient attains across all these marker-specific fits.

**Random-effect model (REM).** Candidate pseudo-QTN sets are scored by the likelihood of

$$y_i = u_i + e_i, \qquad u \sim \mathcal{N}(0,\ 2K\sigma_a^2),$$

where the kinship $K$ is computed from the candidate pseudo QTNs only, so the only unknown parameters are $\sigma_a^2$ and $\sigma_e^2$, whatever the number of pseudo QTNs. Candidates are built by dividing the genome into bins and taking the most significant marker of each bin; bin size and number are chosen to optimize the REML criterion, the number of pseudo QTNs is capped by a function of sample size (for example $n/\log_{10}n$), and of two pseudo QTNs with correlation above a threshold (for example $0.7$) the less significant one is dropped.

**Iteration.** Start from known candidates (or the empty set); run the FEM with substitution; stop if no marker passes the multiple-testing threshold; otherwise update the pseudo QTNs from the REM and repeat until the set no longer changes or a maximum number of iterations is reached.

**Complexity.** For a fixed number of iterations and pseudo QTNs, the FEM scan costs $O(nm)$ and the REM, solved through a low-rank decomposition of the pseudo-QTN genotype matrix, costs $O(n)$, so FarmCPU runs in $O(nm)$ time with $O(nt)$ memory.

## Remarks

In a standard mixed-model scan the kinship is built from all markers, including the tested marker and markers in linkage disequilibrium with it, so the random effect partly absorbs the very signal under test ("proximal contamination"). FarmCPU separates the two roles: the population-structure and polygenic background controls in the FEM are fixed-effect pseudo QTNs, while the kinship in the REM is used only to select those pseudo QTNs and never enters the marker test. Because every marker is tested with the pseudo QTNs as covariates, markers whose association is explained by a pseudo QTN do not show inflated $P$ values, while a pseudo QTN cannot be tested against itself, which is why substitution assigns it the best $P$ value over all fits. Restricting the kinship to $t \ll n$ pseudo QTNs makes the REM a two-parameter problem whose likelihood can be evaluated from the singular value decomposition of an $n \times t$ matrix, avoiding the $O(n^2)$ kinship and $O(n^3)$ eigendecomposition of a full genomic relationship matrix.

## Sources

- X. Liu, M. Huang, B. Fan, E. S. Buckler and Z. Zhang, "Iterative Usage of Fixed and Random Effect Models for Powerful and Efficient Genome-Wide Association Studies", *PLoS Genetics* 12 (2016), e1005767, Introduction "Idea", Materials and Methods "FarmCPU method" (Equations (3)–(4) and Steps 1–7) and Results "Theoretical complexity", <https://doi.org/10.1371/journal.pgen.1005767> (PMC4734661).
