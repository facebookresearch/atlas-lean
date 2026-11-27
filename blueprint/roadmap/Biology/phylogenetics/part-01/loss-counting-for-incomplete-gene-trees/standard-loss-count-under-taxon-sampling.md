# Standard loss count of an incomplete gene tree under taxon sampling

Let $ST$ be a rooted binary species tree and $gt$ a rooted binary gene tree whose leaves are labelled by species, possibly with repeats, with leaf-species set $L(gt) \subseteq L(ST)$; $gt$ is **incomplete** if $L(gt) \ne L(ST)$. The **LCA mapping** is $M(v) = \mathrm{MRCA}_{ST}(c_{gt}(v))$, where $c_{gt}(v)$ is the set of species below $v$; an internal node $v$ is a **duplication** if $M(v) = M(v')$ for a child $v'$, and a **speciation** otherwise. Let $ST(gt)$ be the restriction of $ST$ to $L(gt)$ with degree-2 nodes suppressed, and for an internal node $u$ of $gt$ with children $l, r$ and a species tree $S$ set

$$F(u, S) = \begin{cases} d(M(r), M(u)) + 1 & M(r) \ne M(u) = M(l),\\ d(M(l), M(u)) + 1 & M(l) \ne M(u) = M(r),\\ d(M(r), M(u)) + d(M(l), M(u)) & M(r) \ne M(u) \ne M(l),\\ 0 & M(r) = M(l) = M(u), \end{cases}$$

where $d(s, s')$ is the number of internal nodes of $S$ strictly between $s$ and $s'$. The **standard loss count** is $L_{std}(gt, ST) = \sum_{u} F(u, ST(gt))$.

A **completion** of $gt$ is a complete binary gene tree obtained by inserting every missing species (at least once, possibly several times). Let $L_{samp}(gt, ST)$ be the minimum of $L_{std}(t, ST)$ over completions $t$ of $gt$: the loss count when missing taxa are attributed to incomplete sampling.

**Theorem 1.** For every such $gt$ and $ST$, the LCA mapping is a reconciliation minimizing the number of duplications, the number of losses and their sum when incompleteness is due to sampling, and

$$L_{std}(gt, ST) = L_{samp}(gt, ST).$$

Moreover some completion $t^*$ attains simultaneously the minimum number of duplications and of losses.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Proof depends on

- [Optimality of the LCA reconciliation](../../../not-yet-classified/lcareconciliation/lca-optimal.md)

## Expansion

Completing a gene tree can never remove losses or duplications, so it suffices to build a completion with the same counts. First, if $M(r(gt)) \ne r(ST)$, graft $gt$ in place of the subtree of $ST$ rooted at $M(r(gt))$; the upper missing clades hang off the path to the root and add neither losses nor duplications. Then insert each lower maximal missing clade $t$ (a maximal clade of $ST$ containing no species of $gt$, below $M(r(gt))$) by subdividing every edge $(x, y)$ of the current tree whose image path passes through the parent $q$ of $r(t)$ and hanging a copy of $t$ there. LCA images of existing nodes do not change, the new nodes are speciations, and a case check gives $F(y) = F'(y) + F'(u)$ at each subdivision, so the loss total is preserved. Induction on the number of lower maximal missing clades finishes the proof.

## Sources

- M. S. Bayzid, T. Warnow, "Gene tree parsimony for incomplete gene trees: addressing true biological loss", Algorithms for Molecular Biology 13:1 (2018), Theorem 1 and Eq. (1), <https://doi.org/10.1186/s13015-017-0120-1>, PMCID PMC5774205.
