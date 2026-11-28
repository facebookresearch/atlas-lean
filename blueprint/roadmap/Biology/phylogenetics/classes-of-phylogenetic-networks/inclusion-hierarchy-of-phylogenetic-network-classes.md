# Inclusion hierarchy of phylogenetic network classes

Within rooted binary phylogenetic networks on $X$ consider the classes: **normal** (tree-child without shortcuts, where a shortcut is an arc $(u,v)$ such that another directed path from $u$ to $v$ exists); **tree-child**; **tree-sibling** (every reticulation has a sibling of in-degree one, that is, a sibling that is a tree vertex or a leaf); **reticulation-visible** (every reticulation is visible); **galled trees** (all reticulation cycles, i.e. pairs of internally vertex-disjoint directed paths with common endpoints, are pairwise vertex-disjoint); **stack-free** (no reticulation is the parent of a reticulation); **orchard** (reducible to a single leaf by [cherry and reticulated-cherry reductions](../orchard-phylogenetic-networks/orchard-networks-and-cherry-picking.md)); and **tree-based**.

**Proposition.** The following inclusions hold:

1. normal $\subseteq$ tree-child;
2. tree-child $\subseteq$ tree-sibling $\subseteq$ tree-based;
3. tree-child $\subseteq$ reticulation-visible $\subseteq$ stack-free $\subseteq$ tree-based, and reticulation-visible $\subseteq$ tree-based;
4. tree-child $\subseteq$ orchard $\subseteq$ tree-based;
5. galled trees $\subseteq$ tree-child.

## Depends on

- [Tree-child networks](tree-child-networks.md)
- [Tree-based networks and support trees](tree-based-networks-and-support-trees.md)
- [Orchard networks and cherry picking](../orchard-phylogenetic-networks/orchard-networks-and-cherry-picking.md)

## Proof depends on

- [HGT-consistent labellings characterize orchard networks](../orchard-phylogenetic-networks/hgt-consistent-labellings-characterize-orchard-networks.md)

## Expansion

(1) holds by definition, and tree-child $\subseteq$ reticulation-visible because every vertex of a tree-child network is visible. For tree-child $\subseteq$ tree-sibling, a reticulation $r$ with parents $p_1, p_2$ in a tree-child network has, among the children of each $p_i$, a child of in-degree one (a tree vertex or a leaf), and that child is a sibling of $r$. A leaf sibling must be allowed: if the root has children $p, q$, with children $a, h$ and $b, h$ respectively, and the reticulation $h$ has the leaf child $c$, the network is tree-child but the only siblings of $h$ are the leaves $a$ and $b$. Tree-sibling $\subseteq$ tree-based is Corollary 2 of Francis and Steel; reticulation-visible $\subseteq$ stack-free is Theorem 2.1 of Semple and Simpson, and stack-free networks, being covered by two embedded phylogenetic trees, are tree-based. The orchard inclusions are due to Janssen and Murakami (tree-child $\subseteq$ orchard) and Huber et al. (orchard $\subseteq$ tree-based; for binary networks it also follows from HGT-consistent labellings), and galled trees are tree-child by Huson, Rupp and Scornavacca (Lemma 6.11.11). The survey's examples (its Figure 4) show some inclusions are strict: a tree-sibling network in which a reticulation's only child is a reticulation is not tree-child, and a stack-free network may contain sibling reticulations, which a tree-child network cannot.

## Sources

- S. Kong, J. C. Pons, L. Kubatko and K. Wicke, "Classes of explicit phylogenetic networks and their biological and mathematical significance", Journal of Mathematical Biology 84 (2022), 47, <https://doi.org/10.1007/s00285-022-01746-y>. Section 3.3, Table 1 (inclusions 3, 5, 7, 8, 9, 13, 19, 21, 22, 24) and Figure 12.
