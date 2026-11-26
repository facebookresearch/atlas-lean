# Infinite-sites conditional likelihood over mutation allocations

Let $Y$ be binary sequence data at $s$ segregating sites from $n$ fully linked haploid sequences under the infinite-sites model with known ancestral states and mutation rate $\mu$. Compress $Y$ into $Y_{h \times m}$ by recording the $h$ distinct haplotypes with their frequencies and grouping identical columns into $m$ mutation groups with their cardinalities; by Gusfield's perfect-phylogeny algorithm this compressed representation is in one-to-one correspondence with the gene tree $T$ of the data, so $\Pr(Y \mid g^T, \mu) = \Pr(T \mid g^T, \mu)$ for a Tajima's genealogy $g^T$.

Mutations fall on the branches of $g^T$ as a Poisson process of rate $\mu$, so the conditional likelihood is obtained by summing over all allocations of the observed mutation groups to branches that are compatible with the gene tree. Organizing the allocations on a directed acyclic graph whose nodes carry the counts assigned to each branch, every node contributes a factor $e^{-\mu \mathcal L}$ (global, with $\mathcal L$ the total length of $g^T$) times $(\mu l_j)^{x}$ for a single branch of length $l_j$ receiving $x$ mutations, and for a node whose parent allocates to $k > 1$ branches,

$$\Pr\bigl(X_i = (x_{i1},\dots,x_{ik}) \mid \mathbf b = (b_{j_1},\dots,b_{j_k}), g^T, \mu\bigr) \;\propto\; \sum_{\mathbf s \in \Pi(x_i,k)} \prod_{r=1}^{k} (\mu l_{j_r})^{s_r},$$

where $\Pi(x_i,k)$ is the set of distinct permutations of the multiset $x_i$ over the $k$ branches, of cardinality

$$|\Pi(x_i,k)| = \frac{k!}{\prod_{j=1}^{m_i} k_j!}$$

when the multiset has $m_i$ distinct values with multiplicities $k_1, \dots, k_{m_i}$. Marginalizing the directed acyclic graph from tips to root by backtracking computes $\Pr(Y \mid g^T, \mu)$ exactly.

When ancestral states are unknown, the data form an unlabelled *unrooted* gene tree $Y^0$ compatible with at most $s+1$ unlabelled rooted gene trees $Y^{(i)}$, and

$$\Pr(Y^0 \mid g^T, \mu) = \sum_{i=1}^{\mathcal R(Y^0)} \Pr(Y^{(i)} \mid g^T, \mu),$$

with $\mathcal R(Y^0)$ the number of those rootings.

## Depends on

- [Density of a Tajima's genealogy under a variable population size](tajima-genealogy-density-under-a-variable-population-size.md)
- [Infinite-sites mutation on a finite genealogy](../../poisson-mutation-on-the-kingman-genealogy/branch-mutation-kernel.md)
- [Perfect phylogeny and the four-gamete condition](../../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/exists-perfect-phylogeny-iff.md)

## Expansion

The gene tree is a multifurcating tree of haplotypes, not the bifurcating genealogy of individuals: each row of $Y_{h\times m}$ is a leaf, each mutation group is an edge carrying the number of sites in that group, and the path from the root to a leaf spells out the haplotype. Compatibility of an allocation means every mutation group is placed on a branch of $g^T$ whose descendant leaves are exactly the carriers of that group, which is why only ranked tree shapes, and not leaf labels, matter: individuals are exchangeable, and the data constrain only which nested subsets of the sample carry which groups. The permutation count arises because the mutation groups attached to a node can be assigned to its $k$ candidate branches in any order, equal counts being indistinguishable; for example the multiset $\{2,2,2,0,3,3\}$ over six branches admits $6!/(3!\,1!\,2!) = 60$ assignments. Combining this conditional likelihood with the Tajima's genealogy prior gives a posterior over $(N(\cdot), g^T, \tau)$ that can be sampled directly from sequence data, without first estimating a labelled genealogy.

## Sources

- J. A. Palacios, A. Véber, L. Cappello, Z. Wang, J. Wakeley, S. Ramachandran, "Bayesian estimation of population size changes by sampling Tajima's trees", *Genetics* 213 (2019), 967–986, <https://doi.org/10.1534/genetics.119.302373> (PMC6827370). Materials and Methods, "Summarizing sequence data as haplotypes and mutation groups", "An augmented data representation using directed acyclic graphs", "Computing the conditional likelihood" and "The case of unknown ancestral states", Equations (6) and (7).
- D. Gusfield, "Efficient algorithms for inferring evolutionary trees", *Networks* 21 (1991), 19–28, <https://doi.org/10.1002/net.3230210104>.
