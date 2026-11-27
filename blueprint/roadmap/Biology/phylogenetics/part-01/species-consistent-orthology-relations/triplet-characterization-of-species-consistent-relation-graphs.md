# Triplet characterization of species-consistent relation graphs

**Setting.** A gene family is a set $\Gamma$ of genes with a species map $s:\Gamma \to \Sigma$; a species tree $S$ has leaf set $\Sigma$. A *DS-tree* for $\Gamma$ is a rooted tree $G$ with leaf set $\Gamma$ whose internal nodes are labelled $\mathrm{Spec}$ (speciation) or $\mathrm{Dup}$ (duplication). The LCA-mapping sends a leaf $g$ to $s(g)$ and an internal node $v$ to $s_G(v) = \mathrm{lca}_S\{s(g) : g \in L(G_v)\}$. Two genes $x,y$ are *orthologous* in $G$ if $\mathrm{lca}_G(x,y)$ is a speciation and *paralogous* otherwise; $O(G)$ and $P(G)$ denote these sets of pairs.

**Definition 1 (S-consistency).** A speciation node $v$ of $G$ is $S$-consistent if for any two distinct children $v_1,v_2$ of $v$, the species $s_G(v_1)$ and $s_G(v_2)$ are separated in $S$ (neither is an ancestor of the other). $G$ is $S$-consistent if all its speciation nodes are.

**Relation graphs.** A relation graph $R$ on vertex set $\Gamma$ has an edge $xy$ for each orthologous pair and a non-edge for each paralogous pair. $R$ is *satisfiable* if $R = R(G)$ for some DS-tree $G$, and *$S$-consistent* if it is satisfied by some $S$-consistent DS-tree. Define the set of species triplets induced by paths on three vertices

$$P_3(R) = \{\, s(x)s(y)|s(z) \;:\; zx, zy \in E(R),\ xy \notin E(R),\ s(x) \ne s(y) \,\}.$$

**Theorem 1.** $R$ is satisfiable iff $R$ is $P_4$-free, i.e. no four vertices induce a path with three edges.

**Lemma 1.** If $S$ is binary and $G$ is an $S$-consistent DS-tree, there is a binary $S$-consistent DS-tree $G'$ with $O(G') = O(G)$ and $P(G') = P(G)$.

**Theorem 2.** Let $R$ be a satisfiable relation graph and $S$ a species tree. Then $R$ is $S$-consistent iff $S$ displays every triplet of $P_3(R)$.

## Depends on

- [Rooted triplet](../../splits-compatibility-ultrametrics-and-upgma/triplet.md)
- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Necessity in Theorem 2: if $z$ is orthologous to both $x$ and $y$ while $x,y$ are paralogous, then in any satisfying tree $\mathrm{lca}_G(x,y)$ is a duplication strictly below the speciation $\mathrm{lca}_G(x,z) = \mathrm{lca}_G(y,z)$, so $G$ contains the gene triplet $xy|z$; $S$-consistency of that speciation forces $S$ to display $s(x)s(y)|s(z)$. Sufficiency builds the cotree of the cograph and uses that every internal node $v$ has leaves $x,y$ below it with $\mathrm{lca}_S(s(x),s(y)) = s_G(v)$ and $\mathrm{lca}_G(x,y) = v$ (Lemma 2). Lemma 1 refines non-binary nodes along $S$, so the results hold for binary and non-binary gene trees alike. Theorem 2 gives a polynomial test for $S$-consistency, which is the certificate check in the hardness results.

## Sources

- M. Lafond, R. Dondi, N. El-Mabrouk, "The link between orthology relations and gene trees: a correction perspective", Algorithms for Molecular Biology 11 (2016) 4, Definitions 1–2, Theorem 1 (restated from earlier work), Lemmas 1–2, Theorem 2, <https://doi.org/10.1186/s13015-016-0067-7>, PMCID PMC4833969.
