# Unique generation of tree-child and normal networks by leaf and reticulation insertion

**Setting.** A rooted binary phylogenetic network on $[1,n]$ has a root of indegree $0$ and outdegree $1$, tree nodes (indegree $1$, outdegree $2$), reticulations (indegree $2$, outdegree $1$), $n$ labelled leaves, and no parallel edges. An edge is a *tree edge* if it enters a tree node or a leaf. The network is *tree-child* if every non-leaf node has a child that is a tree node or a leaf, and *normal* if it is tree-child and the two parents of every reticulation are incomparable (neither is an ancestor of the other). Two edges $(u_1,v_1),(u_2,v_2)$ are incomparable if neither of $v_1,v_2$ is an ancestor of the other. Let $\mathrm{TCN}_k(n)$ be the set of tree-child networks on $[1,n]$ with $k$ reticulations.

**Operations** on $N\in\mathrm{TCN}_k(n)$:

- *Leaf insertion* $\mathrm{LeafInsert}(N,e,n+1)$: subdivide a tree edge $e$ by a new tree node $w$ and attach leaf $n+1$ as a child of $w$.
- *Reticulation insertion* $\mathrm{RetInsert}(N,e_1,e_2,n+1)$: subdivide tree edges $e_1,e_2$ (possibly $e_1=e_2$) by new nodes $w_1,w_2$, add a reticulation $r$ with parents $w_1,w_2$, and make leaf $n+1$ the child of $r$.
- *Child rotation* $\mathrm{CRotate}(N,u,r)$: for a reticulation $r$ with parents $u$ (a tree node) and $v$, where $u$ is not an ancestor of $v$, exchange the child of $r$ with the other child of $u$. This is a special case of a rooted nearest-neighbour interchange.

**Theorem (tree-child networks).** Every $N\in\mathrm{TCN}_{k+1}(n+1)$ is obtained in exactly one of the following ways:

1. from a unique $M\in\mathrm{TCN}_{k+1}(n)$ by attaching leaf $n+1$ to a tree edge; or
2. from a unique $M\in\mathrm{TCN}_k(n)$ by
   (a) inserting a reticulation $r$ with child $n+1$ into one tree edge or straddling two tree edges;
   (b) inserting $r$ into one tree edge $(u,v)$ and then rotating so that $v$ becomes the child of $r$ and $n+1$ the child of the inserted tree node above $v$; or
   (c) inserting $r$ straddling tree edges $(u',v')$ and $(u'',v'')$ and then rotating so that $v''$ becomes the child of $r$ (allowed if $v''$ is not an ancestor of $v'$), or symmetrically $v'$ (allowed if $v'$ is not an ancestor of $v''$).

The source's Theorem 1(c) prints the side condition as "if $u''$ (resp. $u'$) is not an ancestor of $u'$ (resp. $u''$)". The page states the condition of its own CRotate step instead: the rotation is $\mathrm{CRotate}$ at the node $w''$ inserted in $(u'',v'')$, which requires that $w''$ is not an ancestor of the other parent $w'$ of $r$, that is, that $v''$ is not an ancestor of $v'$. With the printed condition some networks arise in no way (for example, from $M$ with edges $\rho\to a$, $a\to b$, $a\to3$, $b\to1$, $b\to2$, inserting $r$ straddling $(b,1)$ and $(a,3)$ and rotating $3$ under $r$), and the count of $\mathrm{TCN}_1(4)$ comes out as $222$ rather than $228$.

**Theorem (normal networks).** Every normal network in $\mathrm{TCN}_{k+1}(n+1)$ arises either from a unique normal network in $\mathrm{TCN}_{k+1}(n)$ by leaf insertion, or from a unique normal $N\in\mathrm{TCN}_k(n)$ and a pair of incomparable edges $e_1=(u_1,v_1)$, $e_2=(u_2,v_2)$ by inserting $r$ straddling $e_1,e_2$ and optionally rotating $v_1$ (resp. $v_2$) to be the child of $r$. The rotation onto $v_1$ is excluded exactly when $N$ has a reticulate edge $(x,y)$ with $y$ below $v_1$, $x$ not an ancestor of $v_1$, and $x$ an ancestor of $v_2$, and symmetrically for $v_2$.

## Expansion

This generalizes the classical fact that all phylogenetic trees on $[1,n+1]$ arise exactly once by inserting leaf $n+1$ into every edge of every tree on $[1,n]$. Uniqueness comes from deleting leaf $n+1$. If its parent is a tree node whose sibling is not a reticulation, suppressing the parent undoes a leaf insertion. If its parent is a reticulation, deleting the reticulation and its two parents undoes a reticulation insertion; the case analysis on whether those parents are adjacent separates (a) from (b). If its sibling is a reticulation, a single child rotation first moves $n+1$ under a reticulation, which gives cases (b) and (c). Each step keeps the network acyclic and tree-child. For normal networks, deleting $n+1$ preserves normality. A rotation can break the normal condition at an existing reticulation, and the stated exclusion removes exactly those rotations.

## Sources

- L. Zhang, "Generating normal networks via leaf insertion and nearest neighbor interchange", *BMC Bioinformatics* 20 (Suppl 20):642 (2019), Section "Generating TCNs and normal networks" (operation definitions, Propositions 1–4), Theorems 1 and 2, <https://doi.org/10.1186/s12859-019-3209-3>, PMCID PMC6915859.
