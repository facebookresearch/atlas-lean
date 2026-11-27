# Semidominators

Let $G = (V, E, r)$ be a flowgraph: a finite directed graph with a start vertex $r$ from which every vertex is reachable. Number the vertices $1, \dots, n$ in the order in which a [depth-first search](../../../graph-algorithms/traversal-and-connectivity/depth-first-search/dfs.md) from $r$ first reaches them, identify each vertex with its number, and let $T$ be the spanning tree of the search. Write $v \xrightarrow{*} w$ when $v$ is an [ancestor](../../../graph-algorithms/traversal-and-connectivity/strongly-connected-components/tree-ancestor.md) of $w$ in $T$, and $v \xrightarrow{+} w$ when moreover $v \ne w$.

The *semidominator* of a vertex $w \ne r$ is

$$\mathrm{sdom}(w) = \min\{v \mid \text{there is a path } v = v_0, v_1, \dots, v_k = w \text{ in } G \text{ with } v_i > w \text{ for } 1 \le i \le k - 1\}.$$

It satisfies the following, where $\mathrm{idom}(w)$ is the immediate dominator of $w$:
- *(paths lemma)* if $v \le w$, every path from $v$ to $w$ contains a common ancestor of $v$ and $w$ in $T$;
- $\mathrm{idom}(w) \xrightarrow{+} w$ and $\mathrm{sdom}(w) \xrightarrow{+} w$;
- $\mathrm{idom}(w) \xrightarrow{*} \mathrm{sdom}(w)$.

Replacing the nontree edges of $G$ by the edges $(\mathrm{sdom}(w), w)$, for $w \ne r$, leaves the dominators of all vertices unchanged.

## Depends on

- [Dominance and static single assignment form](../dominance-and-static-single-assignment-form.md)
- [Left-first depth-first search](../../../graph-algorithms/traversal-and-connectivity/depth-first-search/dfs.md)
- [Ancestor in a depth-first spanning forest](../../../graph-algorithms/traversal-and-connectivity/strongly-connected-components/tree-ancestor.md)

## Sources

- T. Lengauer and R. E. Tarjan, "A fast algorithm for finding dominators in a flowgraph", *ACM Transactions on Programming Languages and Systems* 1(1):121–141, 1979: Section 2, the depth-first numbering, Lemma 1 (the paths lemma), the definition (1) of $\mathrm{sdom}$, the remarks that follow it, and Lemmas 2, 3 and 4.
