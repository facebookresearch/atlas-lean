# An anomalous root subtree makes the whole species tree anomalous

Let $\sigma$ be a [species tree](species-tree.md) with labelled topology $\psi$ whose two subtrees below the root are $S$, with labelled topology $L_S$, and $S'$, with labelled topology $L_{S'}$, one lineage
per species. Suppose that $L_S$ produces anomalies on its own: for some branch lengths $B_S$ there is a labelled topology $L^*$ whose probability $q_2$ under the
[multispecies coalescent](gene-tree-prob.md) on $S$ exceeds the probability $q_1$ of $L_S$. Then $\psi$ produces anomalies. Choose $\alpha < 1 - q_1/q_2$ and make the branches of $S'$ and the
branch above it long enough that, with probability greater than $1 - \alpha$, every coalescence in $S'$ happens on the first branch where it can and the lineages of $S'$
coalesce below the root of $\sigma$. Give $S$ the lengths $B_S$, and make the branch above $S$ long enough that the lineages of $S$ coalesce below the root with probability greater
than $1 - \varepsilon$, where $\varepsilon < ((1 - \alpha)q_2 - q_1)/(2 - \alpha)$. Then the gene tree matching $\psi$ has probability at most $\varepsilon + q_1$, while the topology $\psi^*$ whose root subtrees
are $L_{S'}$ and $L^*$ has probability at least $(1 - \alpha)(q_2 - \varepsilon)$, and the choice of $\varepsilon$ gives $(1 - \alpha)(q_2 - \varepsilon) > \varepsilon + q_1$.

## Depends on

- [The multispecies coalescent](gene-tree-prob.md)

## Expansion

The record's broader form (any species tree on $k + 1$ taxa that restricts to an anomalous tree on $k$ taxa) is not stated here; the source proves the case in
which the anomalous tree is one of the two subtrees below the root.

## Sources

- J. H. Degnan and N. A. Rosenberg, "Discordance of species trees with their most likely gene trees", PLoS Genetics 2 (2006), e68, <https://doi.org/10.1371/journal.pgen.0020068>, proof of Proposition 2.
