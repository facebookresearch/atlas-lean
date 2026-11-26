# Polynomial-time probability of a ranked gene tree

**Setting.** Let $T$ be a rooted binary species tree on $n$ species with speciation times $s_1 > \cdots > s_{n-1}$ (and $s_0 = \infty$), defining intervals $\tau_i = [s_i, s_{i-1})$; within each interval the species tree has $i$ ancestral populations $y_{i,z}$. One gene is sampled per species and its genealogy follows the multispecies coalescent: within each population every pair of lineages coalesces at rate $1$ (time in coalescent units). A *ranked gene tree* $G$ is a rooted gene tree topology with internal nodes $u_1, \dots, u_{n-1}$ ordered by time ($u_1$ the oldest). For each $i$, let $(G_i, \ell_i)$ denote the event that the part of $G$ formed between time $0$ and $s_i$ is realized with $\ell_i$ lineages remaining at $s_i$, let $g_i$ be the minimum feasible $\ell_i$ (from LCA constraints), $m_i = \ell_i - \ell_{i-1}$ the number of coalescences in $\tau_i$, $k_{i,j,z}$ the number of lineages in population $y_{i,z}$ just after the $j$th coalescence in $\tau_i$ (forward in time), and $\lambda_{i,j} = \sum_z \binom{k_{i,j,z}}{2}$ the total coalescence rate in that stretch.

**Theorem.**

1. $P[G \mid T] = \sum_{\ell_1 = g_1}^{n} P[G_1, \ell_1 \mid T] / H_{\ell_1}$, where $H_\ell = \ell!(\ell-1)!/2^{\ell-1}$ is the number of orders of the coalescences of $\ell$ lineages above the root, each equally likely.
2. For all $i$ (with $\ell_i \ge g_i$),

$$P[G_i, \ell_i \mid T] = \sum_{\ell_{i+1} = \max(\ell_i, g_{i+1})}^{n} P[G_i, \ell_i \mid G_{i+1}, \ell_{i+1}, T]\; P[G_{i+1}, \ell_{i+1} \mid T].$$

3. The transition probability for the $m_i$ prescribed coalescences in interval $\tau_i$ is

$$P[G_{i-1}, \ell_{i-1} \mid G_i, \ell_i, T] = \sum_{j=0}^{m_i} \frac{e^{-\lambda_{i,j}(s_{i-1} - s_i)}}{\prod_{k=0,\,k\ne j}^{m_i} (\lambda_{i,k} - \lambda_{i,j})}.$$

4. All $g_i$, $k_{i,j,z}$, $\lambda_{i,j}$ and transition probabilities can be computed in $O(n^5)$ time, so $P[G \mid T]$ is computable in $O(n^5)$ time.

Consequently the probability of an unranked gene tree topology is computable in polynomial time whenever it has polynomially many rankings.

## Depends on

- [Rooted binary species tree with branch lengths](../species-tree.md)
- [The multispecies coalescent](../gene-tree-prob.md)
- [Ranked labeled history](../../ranked-labeled-histories-of-coalescent-trees/ranked-history.md)

## Proof depends on

- [Holding times of Kingman's coalescent](../../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)

## Expansion

Ranking fixes which pair coalesces at each step, so within an interval the process is a chain of prescribed events, each with rate $1$, waiting in states with total rates $\lambda_{i,0}, \dots, \lambda_{i,m_i}$; the probability that exactly these events occur within the interval length is the hypoexponential expression in item 3. Conditioning on the number of lineages at each speciation time gives a Markov recursion over $i$ (item 2) whose state space is only $O(n)$ per interval, which removes the exponential sum over coalescent histories used by earlier unranked methods. Above the root all $\ell_1$ lineages share one population, and each of the $H_{\ell_1}$ coalescence orders is equally likely.

## Sources

- T. Stadler and J. H. Degnan, "A polynomial time algorithm for calculating the probability of a ranked gene tree given a species tree", *Algorithms for Molecular Biology* (2012), Table 1 (notation), Theorems 1–3 (Eqs. 1–4), Corollaries 4–5 and Section "An algorithm". <https://doi.org/10.1186/1748-7188-7-7> (PMC3637458)
