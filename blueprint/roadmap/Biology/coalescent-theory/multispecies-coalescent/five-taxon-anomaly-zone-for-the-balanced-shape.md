# The five-taxon balanced species tree has an anomaly zone

Let $T$ be a [species tree](species-tree.md) with the balanced topology $((D, E), (C, (A, B)))$, written below as $(((A, B), C), (D, E))$, on five species and one lineage per species; it is a most
probable labelled five-taxon topology under the Yule model (probability $1/60$), so short branches alone do not produce an anomaly. Instead let the branches between the root and
the ancestor of $A, B$ have total length $\lambda$ and the branch above the ancestor of $D, E$ have length $x + y$. For $\varepsilon > 0$ choose $\lambda$ small and $x + y$ large, so
that with probability at least $1 - \varepsilon$ the lineages of $D$ and $E$ have coalesced and no other coalescence has occurred when the root is reached. The four
remaining lineages $A, B, C, Z$ then coalesce by [random joining](random-joining-real.md): of the $18$ ranked histories, one gives $(((A, B), C), Z)$ and two give $((A, B), (C, Z))$. Hence, under
the [multispecies coalescent](gene-tree-prob.md), the gene tree matching $T$ has probability at most $\varepsilon + (1 - \varepsilon)/18$ and the gene tree $((A, B), (C, (D, E)))$ at least $(1 - \varepsilon)/9$, which is
larger when $\varepsilon < 1/19$. The five-taxon tree behaves like the four-taxon caterpillar $(((A, B), C), Z)$ with $Z = (D, E)$, which is in its [anomaly zone](caterpillar-exists-anomalous-iff.md).

## Depends on

- [The multispecies coalescent](gene-tree-prob.md)

## Proof depends on

- [Random-joining probability as a fraction of ranked histories](random-joining-real.md)

## Related topics

- [The four-species anomaly zone](caterpillar-exists-anomalous-iff.md)

## Sources

- J. H. Degnan and N. A. Rosenberg, "Discordance of species trees with their most likely gene trees", PLoS Genetics 2 (2006), e68, <https://doi.org/10.1371/journal.pgen.0020068>, Lemma 5, case $n = 5$, and Figure 3a.
