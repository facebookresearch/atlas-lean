# Treewidth algorithms for hardwired, softwired and parental parsimony

**Setting.** A phylogenetic network $N$ is a rooted DAG with arc set $A(N)$; leaves carry character states from a finite set $C$ of size $c$, generalized to an allowed-state map $\phi : V(N) \to 2^C$. Three parsimony scores extend the [small parsimony problem](../../small-parsimony-problem/sankoff.md) from trees to networks:

- *hardwired*: minimize, over state assignments respecting $\phi$, the number of arcs of $N$ whose endpoints have different states (each node inherits from all parents);
- *softwired*: minimize the same count over the arcs of a *switching*, a choice of one incoming arc at each reticulation (each character inherited from one parent);
- *parental*: allow lineages of each allele to be embedded in the network, each inherited from one parent.

All three are NP-hard. Let $t \ge tw(N)$ be the treewidth of the underlying undirected graph and $T$ the time to compute a width-$t$ tree decomposition.

**Theorem.** Given a rooted tree $\Gamma$ agreeing with $N$ (in particular one of width $yw(\Gamma) = t$ obtained from the tree decomposition):

1. the hardwired score can be computed in $O(|C|^{yw(\Gamma)+1} \cdot |A(N)|)$ time, hence in $O(T + c^{t+1}|A(N)|)$;
2. the softwired score in $O\bigl(|C|^{yw(\Gamma)}(3^{yw(\Gamma)} |C| |V(N)| + |A(N)|)\bigr)$ time, hence in $O\bigl(T + c^t(3^t c\,|V(N)| + |A(N)|)\bigr)$;
3. the parental score in $O\bigl(6^{yw(\Gamma)|C|} \cdot 4^{yw(\Gamma)\log|C|} \cdot |A(N)|\bigr)$ time, hence in $O\bigl(T + 6^{tc}\, 4^{t\log c}\, |A(N)|\bigr)$.

In particular all three problems are fixed-parameter tractable in $t + c$ (hardwired and softwired already in $t$ for fixed $c$, with running times $c^t n^{O(1)}$ and $(3c)^t n^{O(1)}$).

## Depends on

- [Treewidth as the minimum width of an agreeing rooted tree](treewidth-as-the-minimum-width-of-an-agreeing-rooted-tree.md)
- [Sankoff's algorithm](../../small-parsimony-problem/sankoff.md)
- [Tree-decomposition](../../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)
- [Tree-width at most $k$](../../../../GraphTheory/planar-graphs-and-minors/tree-width/has-treewidth-at-most.md)

## Expansion

The dynamic program traverses $\Gamma$ bottom-up; at node $v$ a table is indexed by the states of the at most $yw(\Gamma)$ vertices in $YW^\Gamma_v$, which are the only vertices outside the subtree of $v$ that interact with it, and stores the best partial score. For the softwired and parental scores the table entries must additionally encode, for the open vertices, the partial switching or lineage-embedding choices, which accounts for the extra $3^{t}$ and $6^{tc}$-type factors. A tree decomposition of width $t$ can be found in $|N| \cdot 2^{O(t^3)}$ time, or approximately faster.

## Sources

- C. Scornavacca and M. Weller, "Treewidth-based algorithms for the small parsimony problem on networks", *Algorithms for Molecular Biology* (2022), Section "Parsimony" (Fig. 1), Theorems 1–3 and Corollaries 1–3. <https://doi.org/10.1186/s13015-022-00216-w> (PMC9392953)
