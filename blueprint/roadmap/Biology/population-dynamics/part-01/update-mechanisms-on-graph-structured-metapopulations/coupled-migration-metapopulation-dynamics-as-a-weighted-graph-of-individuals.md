# Coupled-migration metapopulation dynamics as a weighted graph of individuals

Consider a graph-structured metapopulation: patches $i = 1, \dots, M$ carry well-mixed subpopulations of fixed sizes $N_i$, with $n_i$ mutants, connected by patch weights $w_{ij} \ge 0$ ($w_{ii} = 0$), with $N = \sum_i N_i$ and $n = \sum_i n_i$. Mutants have birth parameter $r$ relative to the wild type. In the **coupled-migration update MBBdd** each step is:

1. choose a patch $i$ with probability proportional to its collective birth parameter $r n_i + N_i - n_i$, then an individual in it with probability proportional to its birth parameter; it reproduces;
2. with probability $1 - \lambda$ the offspring stays and replaces an individual of patch $i$ chosen uniformly at random; with probability $\lambda$ it migrates to a neighbouring patch $j$ chosen with probability $w_{ij} N_j / \sum_k w_{ik} N_k$ and replaces an individual of patch $j$ chosen uniformly at random.

**Proposition (Appendix C of the source).** MBBdd on the metapopulation is the Bd (birth-biased, uniform death) process on the weighted graph of the $N$ individuals in which an individual of patch $i$ sends its offspring

- to each individual of its own patch (itself included) with weight $(1 - \lambda)/N_i$,
- to each individual of patch $j \ne i$ with weight $\lambda w_{ij} / \sum_k w_{ik} N_k$.

These weights sum to $1$ over all recipients. More generally, a coupled-migration update reduces to an update on a weighted graph of individuals whenever, for each of the birth and death events, selection acts either at both the patch and the individual level or at neither.

## Expansion

The probability that step 1 picks a given mutant of patch $i$ is

$$\frac{r n_i + N_i - n_i}{r n + N - n} \cdot \frac{r}{r n_i + N_i - n_i} = \frac{r}{r n + N - n},$$

the probability of picking that mutant from the whole population in proportion to its birth parameter: two-level selection with matching weights collapses to global selection. In step 2 a given individual of patch $j$ is replaced with probability $\lambda w_{ij} N_j / \sum_k w_{ik} N_k \cdot 1/N_j$, and a given individual of patch $i$ with probability $(1 - \lambda)/N_i$, which are the stated link weights. The reduction shows how local population sizes and the migration probability reweight the links, and why results for graphs of individuals, such as amplification by the star under Bd, need not carry over to metapopulations. Updates that mix patch-level and individual-level selection (for example MbBDD) do not reduce this way; the source classifies 16 birth-first and 16 death-first coupled updates and 16 uncoupled updates in which migration only swaps individuals between patches.

## Depends on

- [Birth-death and death-birth fixation on regular weighted graphs](birth-death-and-death-birth-fixation-on-regular-weighted-graphs.md)

## Sources

- S. Yagoobi, N. Sharma and A. Traulsen, *Categorizing update mechanisms for graph-structured metapopulations*, Journal of the Royal Society Interface 20 (2023), 20220769. DOI: <https://doi.org/10.1098/rsif.2022.0769>. PMCID: PMC10015335.
