# Flattening rank under the multispecies coalescent

Let $\mathcal T$ be a binary species tree on four taxa with speciation times, and let site patterns at the tips arise by integrating over gene trees drawn from the multispecies coalescent on $\mathcal T$, with nucleotides evolving along each gene tree under the four-state general time-reversible (GTR) model. Write

$$p_{ijkl} = \mathbb P(X_1 = i, X_2 = j, X_3 = k, X_4 = l), \qquad i, j, k, l \in \{A, C, G, T\},$$

for the resulting site-pattern distribution $P$. A split $L_1 \mid L_2$ of the four taxa into two pairs is *valid* for $\mathcal T$ if the subtrees spanned by $L_1$ and by $L_2$ do not intersect. The *flattening* $\mathrm{Flat}_{L_1 \mid L_2}(P)$ is the $16 \times 16$ matrix with rows indexed by the states of the two taxa in $L_1$ and columns by the states of the two taxa in $L_2$.

**Theorem.** For a valid split, $\operatorname{rank} \mathrm{Flat}_{L_1 \mid L_2}(P) \le 10$ for every distribution $P$ arising from the model. For each of the two non-valid splits, $\operatorname{rank} \mathrm{Flat}_{L_1 \mid L_2}(P) > 10$ for generic parameters, that is, outside a proper subvariety of parameter space of measure zero.

**Consequence.** The unrooted species-tree topology on four taxa is generically identifiable from the site-pattern distribution of unlinked sites; applying this to all induced quartets gives generic identifiability of the unrooted $n$-taxon species tree under the coalescent.

## Depends on

- [Edge flattenings of the general Markov model have rank at most the number of states](../../phylogenetics/phylogenetic-invariants/flattening-rank-bound-for-the-general-markov-model.md)

## Expansion

For a valid split $\{1,2\} \mid \{3,4\}$, at least one side forms a cherry of the rooted species tree $\mathcal T$; say taxa $1$ and $2$ (otherwise argue with columns). Since they are sampled at the same time, the coalescent gene-tree law and the substitution process are invariant under exchanging their labels: $p_{ijkl} = p_{jikl}$. The rows of the flattening indexed by $(i, j)$ and $(j, i)$ therefore coincide, leaving at most $16 - 6 = 10$ distinct rows. The generic lower bound for non-valid splits is shown by exhibiting one parameter point at which some $11 \times 11$ minor is nonzero; since minors are analytic in the parameters, they then vanish only on a proper subvariety of measure zero.

## Sources

- J. Chifman and L. Kubatko, *Quartet inference from SNP data under the coalescent model*, Bioinformatics 30 (2014), 3317–3324, <https://doi.org/10.1093/bioinformatics/btu530>, PMCID PMC4296144 (Section 1.1, Definition and Theorem 1, which cites the proof in J. Chifman and L. Kubatko, *Identifiability of the unrooted species tree topology under the coalescent model with time-reversible substitution processes*, <https://doi.org/10.1016/j.jtbi.2015.03.006>, arXiv:1406.4811).
