# Cross-population covariance of linkage disequilibrium after a split

Consider two biallelic loci with alleles $A/a$ and $B/b$, separated by recombination fraction $r$ per generation, and write $D = f_{AB}f_{ab} - f_{Ab}f_{aB}$ for the linkage disequilibrium of a population. Suppose an ancestral Wright–Fisher population splits at generation $t_0$ into two isolated randomly mating populations of sizes $N_1(t)$ and $N_2(t)$, with no migration, and let $D_1, D_2$ be their disequilibria. Then, at the split,

$$\mathbb{E}[D_1 D_2]_{t_0} = \mathbb{E}[D^2]_{t_0},$$

the second moment of $D$ in the parental population, and thereafter, to leading order in $1/N_1$, $1/N_2$ and $r$,

$$\mathbb{E}[D_1 D_2]_{t+1} = \left(1 - \frac{1}{2N_1(t)} - \frac{1}{2N_2(t)} - 2r\right)\mathbb{E}[D_1 D_2]_t .$$

Within each population the triple $\bigl(\mathbb{E}[D_i^2], \mathbb{E}[D_i(1-2p_i)(1-2q_i)], \mathbb{E}[p_i(1-p_i)q_i(1-q_i)]\bigr)$ continues to follow the one-population Hill–Robertson system. With continuous migration the system closes only after adding cross-population moments of the forms $\mathbb{E}[D_i z_{j,k}]$, $\mathbb{E}[\pi_2(i,j;k,l)]$ and $\mathbb{E}[H_{i,j}]$, which gives a sparse linear recursion with separate drift, migration, recombination and mutation operators.

## Proof sketch

At the split both daughter populations carry the parental haplotype frequencies, so $D_1 = D_2 = D$ and $\mathbb{E}[D_1D_2] = \mathbb{E}[D^2]$. Afterwards $D_1$ and $D_2$ evolve independently given the split-time state. In each population one generation multiplies the conditional mean of $D_i$ by $(1 - 1/(2N_i) - r)$ to leading order, the same factor as in the one-population recursion for $\mathbb{E}[D]$. Mutation adds zero-mean increments. Taking the product of the two conditional means and dropping second-order terms gives the factor $1 - 1/(2N_1) - 1/(2N_2) - 2r$. Unlike $\mathbb{E}[D_i^2]$, the cross moment has no input from $\mathbb{E}[Dz]$ or $\pi_2$ because the two populations share no parents, so it only decays. Its decay rate against $r$ therefore measures how long ago the split happened.

## Depends on

- [Hill–Robertson and Ohta–Kimura equations, first row](../../coalescent-theory/two-locus-coalescent/two-locus-generator-diseq-sq.md)

## Sources

- A. P. Ragsdale, S. Gravel, *Models of archaic admixture and recent history from two-locus statistics*, PLoS Genetics 15 (2019), e1008204, <https://doi.org/10.1371/journal.pgen.1008204>, PMCID PMC6586359. Hill–Robertson system Eq. (3); split and cross-population recursion Eq. (4); multi-population basis and closed recursion Eqs. (5)–(6).
