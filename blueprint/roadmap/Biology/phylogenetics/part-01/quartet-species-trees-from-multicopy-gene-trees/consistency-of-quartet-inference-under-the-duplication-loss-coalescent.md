# Consistency of quartet inference under the duplication–loss–coalescent model

In the duplication–loss–coalescent (DLCoal) model a *locus tree* first evolves inside a rooted species tree $S = (T_S, w_S)$ with branch lengths by a birth–death process of gene duplications and losses; gene lineages then coalesce backwards in time inside the locus tree under the multilocus coalescent, with a newly duplicated locus founded by a single lineage. The result is a gene tree $G$ whose leaves are labelled by species, possibly with several copies per species. *ASTRAL-one* takes a collection $\mathcal G$ of such gene trees, keeps one copy per species chosen uniformly at random in each tree, and returns the unrooted species tree maximizing the number of induced quartet topologies shared with the input.

1. **Quartet dominance.** Let $S$ have four leaves and display the quartet $AB|CD$, let $G$ evolve in $S$ under DLCoal, and pick genes $a,b,c,d$ of species $A,B,C,D$ uniformly at random from $G$ (conditioning on their existence). Then

    $$\mathbb P[ab|cd \in G] > \mathbb P[ac|bd \in G] = \mathbb P[ad|bc \in G].$$

2. **Consistency.** For any fixed species tree $S$ and gene trees evolving independently in $S$ under DLCoal, the probability that the ASTRAL-one estimate equals the unrooted topology of $T_S$ tends to $1$ as $|\mathcal G| \to \infty$.

## Depends on

- [The multispecies coalescent](../../../coalescent-theory/multispecies-coalescent/gene-tree-prob.md)

## Expansion

Item 2 follows from item 1 because quartet-support maximization is consistent whenever, for every four species, the species-tree quartet is the strictly most probable gene quartet. The proof of item 1 conditions on the locus tree $L$. For any $L$ displaying $ab|cd$, wherever its duplications sit, $\mathbb P[ab|cd \in G \mid L] > \mathbb P[ac|bd \in G \mid L] = \mathbb P[ad|bc \in G \mid L]$. If the root of a balanced $L$ is a duplication, the two pairs are separated by the duplication and $ab|cd$ has probability $1$. Lengthening the internal edge of a caterpillar locus tree only raises the probability of the displayed quartet, since it gives $a$ and $b$ more time to coalesce first. It remains to compare locus-tree topologies. Conditioning on the number of locus lineages at the root speciation of $S$, the duplication–loss process makes locus trees that agree with the species quartet at least as likely as discordant ones, a fact inherited from the consistency proof for the duplication–loss model without coalescence. Treating balanced and caterpillar species trees separately completes the inequality.

## Sources

- A. Markin, O. Eulenstein, "Quartet-based inference is statistically consistent under the unified duplication-loss-coalescence model", *Bioinformatics* (2021), Section 3 (Lemmas 3.1–3.3) and Section 4 (Theorems 4.1–4.2, Lemmas 4.1–4.4, Corollary 4.1), <https://doi.org/10.1093/bioinformatics/btab414> (PMC9113308).
