# HGT-consistent labellings characterize orchard networks

Let $N$ be a binary phylogenetic network with node set $V$. An **HGT-consistent labelling** is a map $t:V\to\mathbb{R}$ such that

1. for every arc $(u,v)$, $t(u)\le t(v)$, with equality allowed only if $v$ is a reticulation;
2. every internal node $u$ has a child $v$ with $t(u)<t(v)$;
3. for every reticulation $r$ with parents $u,v$, exactly one of $t(u)=t(r)$ and $t(v)=t(r)$ holds.

Arcs whose endpoints receive equal labels are called horizontal.

**Theorem (binary case).** A binary network is [orchard](orchard-networks-and-cherry-picking.md) if and only if it admits an HGT-consistent labelling. Moreover every binary orchard network admits one in which two nodes share a label only if they are a tree-node parent and its reticulation child.

**Theorem (non-binary case).** A network is orchard if and only if some binary resolution of it (a binary network that contracts to it) admits an HGT-consistent labelling.

**Corollary.** Deleting all horizontal arcs of an HGT-consistent labelling of a binary network leaves a support tree: a rooted spanning tree whose leaves are exactly the leaves of the network. Its old arc endpoints can have in-degree and out-degree one; suppressing those vertices gives a base tree, so every binary orchard network is [tree-based](../classes-of-phylogenetic-networks/tree-based-networks-and-support-trees.md). The converse fails: a tree-based network containing a crown, nodes $u_1,\dots,u_k,v_1,\dots,v_k$ with arcs $(u_i,v_i)$ and $(u_i,v_{i+1})$ (indices mod $k$), admits no HGT-consistent labelling and is not orchard.

## Depends on

- [Orchard networks and cherry picking](orchard-networks-and-cherry-picking.md)
- [Tree-based networks and support trees](../classes-of-phylogenetic-networks/tree-based-networks-and-support-trees.md)

## Expansion

*Orchard implies labelling.* Take a cherry-picking sequence $(x_1,y_1),\dots,(x_m,y_m)$ and rebuild $N$ by reattaching pairs in reverse order. Label the root $0$, the nodes created when reattaching $(x_i,y_i)$ by $m+1-i$, and the leaves $m+1,\dots,m+n$. New nodes always sit below existing ones with larger labels, and a reticulation is created together with exactly one of its parents, giving properties 1–3.

*Labelling implies orchard.* Take an internal node $x$ with maximal label. If $x$ is a reticulation, its child is a leaf and the parent sharing its label has a leaf as its other child, which gives a reticulated cherry. If $x$ is a tree node, either it has a reticulation child with equal label (again a reticulated cherry) or two leaf children (a cherry); two reticulation children would violate property 2. The restriction of $t$ to the reduced network is still HGT-consistent, so induction reduces $N$ to one leaf.

*Support tree.* By property 3 each reticulation keeps exactly one incoming arc, and by property 1 no arc into a tree node or leaf is horizontal, so after the deletion every non-root node has in-degree one; by property 2 every internal node keeps a child, so no new leaf appears.

*Crown.* The parents of $v_1$ are $u_1$ and $u_k$, and the reflection $u_i\mapsto u_{1-i}$, $v_i\mapsto v_{2-i}$ (indices mod $k$) maps the crown to itself and exchanges them. Property 3 makes exactly one of them share the label of $v_1$; applying the reflection if necessary, assume without loss of generality that $t(u_1)=t(v_1)$. Then property 2 gives $t(u_1)<t(v_2)$, so property 3 at $v_2$ forces $t(u_2)=t(v_2)$, and inductively $t(u_1)<t(u_2)<\dots<t(u_k)<t(v_1)=t(u_1)$, a contradiction. The non-binary case combines the binary theorem with the fact that a network is orchard if and only if some binary resolution is.

## Sources

- L. van Iersel, R. Janssen, M. Jones, Y. Murakami, *Orchard networks are trees with additional horizontal arcs*, Bulletin of Mathematical Biology 84 (2022), <https://doi.org/10.1007/s11538-022-01037-z> (PMCID: PMC9213324). Section 3: Definition 6, Observation 1, the crown argument (Fig. 3), Lemmas 1–2, Theorem 1, Corollary 1, Lemma 3 (quoted from van Iersel et al. 2021) and Theorem 2.
