# Greedy most-frequent-mutation splitting recovers a zero-root perfect phylogeny

**Setting.** Let $C$ be a finite set of cells and $M : C \times \{1, \dots, k\} \to \{s_0, s_1, \dots\}$ a multi-state character matrix without missing entries, where $s_0$ is the unedited state of a Cas9 target site. A *mutation* is a pair $(\chi_i, s_j)$ with $s_j \ne s_0$; its carrier set is $O_{i,j} = \{c \in C : M(c, i) = s_j\}$. A *zero-root perfect phylogeny* for $M$ is a rooted tree whose leaves are the cells, whose internal nodes have at least two children, together with states at internal nodes such that the root has state $s_0$ at every character and every mutation $(\chi_i, s_j)$ arises on at most one edge and is never lost (edited sites cannot be recut). Binarizing each mutation into the character "carries $(\chi_i, s_j)$" turns this into the binary [perfect phylogeny](../../splits-compatibility-ultrametrics-and-upgma/is-perfect-phylogeny.md) condition on carrier sets.

**Greedy algorithm.** On a subset $C' \subseteq C$: if all cells of $C'$ have identical rows, return a star on $C'$ (a single leaf if $|C'| = 1$). Otherwise pick a mutation $(\chi_i, s_j)$ that is carried by some but not all cells of $C'$ and maximizes $|O_{i,j} \cap C'|$ (ties broken arbitrarily), split $C'$ into $O_{i,j} \cap C'$ and $C' \setminus O_{i,j}$, recurse on both parts and join the two returned trees under a new root.

**Theorem.** If $M$ admits a zero-root perfect phylogeny, then the greedy tree, with each mutation placed on the edge above the most recent common ancestor of its carriers, is a zero-root perfect phylogeny for $M$. In particular, the most frequent mutation of the whole matrix labels an edge out of the root of some perfect phylogeny.

## Depends on

- [Perfect phylogeny for a binary character matrix](../../splits-compatibility-ultrametrics-and-upgma/is-perfect-phylogeny.md)

## Expansion

In a zero-root perfect phylogeny each carrier set $O_{i,j}$ is the leaf set below the unique edge where the mutation arises (irreversibility), so the carrier sets form a laminar family: any two are nested or disjoint. Let $(\chi_i, s_j)$ be the mutation chosen on $C'$ and $O = O_{i,j} \cap C'$. If some other carrier set $X$ met both $O$ and $C' \setminus O$, laminarity forces $X \cap C' \supsetneq O$, so $X$ is carried by more cells of $C'$ than the chosen mutation; maximality then forces $X \supseteq C'$, i.e. $X$ is carried by all of $C'$ and was excluded. Hence every mutation that is informative on $C'$ is carried entirely within one side of the split. Restrictions of a perfect phylogeny to a subset of cells are perfect phylogenies, so induction on $|C'|$ shows that each carrier set is a clade of the returned tree, which is exactly the perfect-phylogeny condition. The source proves the theorem by induction from a lemma placing the most frequent mutation on a root edge.

## Sources

- M. G. Jones, A. Khodaverdian, J. J. Quinn, M. M. Chan, J. A. Hussmann, R. Wang, C. Xu, J. S. Weissman and N. Yosef, "Inference of single-cell phylogenies from lineage tracing data using Cassiopeia", Genome Biology 21 (2020), 92, Methods, Definition 1, Lemma 1 and Theorem 1. <https://doi.org/10.1186/s13059-020-02000-8> PMCID: PMC7155257.
