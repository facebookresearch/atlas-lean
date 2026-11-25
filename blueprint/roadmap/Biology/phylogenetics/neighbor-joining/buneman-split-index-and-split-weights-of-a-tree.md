# Buneman split index and split weights of a tree metric

Let $X$ be a finite set with $|X|\ge2$ and let $T$ be an $X$-tree: a finite tree with a map $\iota$ from $X$ to its vertices whose image contains every vertex of degree at most $2$. Give each edge $e$ of $T$ a length $w(e)$, positive on every internal edge, and let $d(x,y)$ be the total length of the path from $\iota(x)$ to $\iota(y)$, a [tree metric](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric.md). Deleting an edge $e$ leaves two components and induces the split of $X$ into the taxa of each component. For a bipartition $A\mid B$ of $X$ ($A,B$ nonempty, disjoint, $A\cup B=X$) the **Buneman index** is

$$\beta(A\mid B)=\min_{\substack{a,a'\in A\\ b,b'\in B}}\tfrac12\bigl(d(a,b)+d(a',b')-d(a,a')-d(b,b')\bigr),$$

where $a=a'$ and $b=b'$ are allowed. Then:

- if $A\mid B$ is the split induced by an edge $e$ of $T$, then $\beta(A\mid B)=w(e)$;
- otherwise $\beta(A\mid B)\le0$.

For example, on a star tree with three leaves $x,y,z$ and pendant lengths $w_x,w_y,w_z$, $\beta(\{x\}\mid\{y,z\})=w_x$; on the quartet tree $ab\mid cd$ with internal length $\ell>0$, the non-split $\{a,c\}\mid\{b,d\}$ has $\beta\le-\ell<0$.

## Depends on

- [Tree metric](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric.md)

## Proof depends on

- [Buneman's four-point theorem](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric-iff-four-point-condition.md)
- [Tree metrics satisfy the four-point condition](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/four-point-condition-2.md)

## Expansion

A proof page must establish the following.

- Each summand equals the length of the path joining the paths $\iota(a)\to\iota(a')$ and $\iota(b)\to\iota(b')$ when these paths are disjoint, and is at most $0$ when they meet, by the [four-point condition](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/four-point-condition-2.md).
- For an edge split, every such joining path contains $e$, so $\beta\ge w(e)$; choosing $a,a'$ whose path passes through the $A$-side endpoint of $e$, and $b,b'$ likewise on the $B$ side (possible because unlabeled vertices have degree at least $3$), gives a summand equal to $w(e)$.
- If $A\mid B$ is not an edge split, the subtrees spanned by $\iota(A)$ and $\iota(B)$ share a vertex, which lies on some path $a\to a'$ and some path $b\to b'$, so some summand is at most $0$.
- The two worked examples above: pendant weights are recovered on a three-leaf tree, and a non-split bipartition of a four-leaf tree has nonpositive index.

## Sources

- P. Buneman, *The recovery of trees from measures of dissimilarity*, in Mathematics in the Archaeological and Historical Sciences, Edinburgh University Press (1971), 387–395 (Buneman index).
- C. Semple and M. Steel, *Phylogenetics*, Oxford University Press (2003) (split systems).
