# Unblended disjoint tree merging with a guide tree

**Definitions.** Trees are unrooted and leaf-labelled by a taxon set $S$. For $S'\subseteq S$, $T|S'$ is the homeomorphic subtree induced on $S'$ (degree-two nodes suppressed). Each tree $t$ is identified with its set $C(t)$ of edge bipartitions, and the false-negative distance is $FN(A,B)=|C(B)\setminus C(A)|$. A **compatibility supertree** for $\mathcal T=\{T_1,\dots,T_k\}$ is a tree $T$ with $L(T)=\bigcup_iL(T_i)$ and $T|L(T_i)=T_i$ for all $i$.

**DTM-GT-FN.** Given leaf-disjoint binary trees $\mathcal T$ (constraint trees) and a guide tree $T^*$ on $S=\bigcup_iL(T_i)$, find a compatibility supertree $T$ minimising $|C(T^*)\setminus C(T)|$. In the **unblended** variant, $T$ must be obtained by connecting the trees of $\mathcal T$ with new edges (so each $T_i$ remains a connected piece of $T$).

**Theorem 1.** DTM-GT-FN is NP-hard.

**Theorem 2 (GTM).** The Guide Tree Merger algorithm solves Unblended DTM-GT-FN optimally in $O(N^2)$ time, $N=|S|$:

1. collapse every edge of $T^*$ whose bipartition, restricted to some $L(T_i)$, is not a bipartition of $T_i$ ("violates a constraint tree");
2. collapse every edge of $T^*$ with two or more constraint sets on both sides ("violates convexity");
3. recursively rejoin: at a border node (an end of a bridge edge, i.e. one with no constraint set on both sides, or a node where edges lying in two different constraint sets meet, refined to separate them) delete an edge $e$, rejoin the two sides, and reconnect them by subdividing, in each side, an edge whose bipartition restricted to that side's constraint sets matches an edge of $T^*$ incident with $e$.

**Theorem 3 (consistency).** If, under a model of evolution $\Phi$, the method computing the starting/guide tree and the method computing the subset trees are both statistically consistent, then the pipeline that decomposes by deleting edges of the starting tree, estimates subset trees and merges them with GTM is statistically consistent under $\Phi$. For example, an NJst starting tree with ASTRAL subset trees gives a pipeline consistent under the multispecies coalescent with GTR sequence evolution.

## Expansion

After steps 1 and 2 every surviving edge of $T^*$ is either a bridge between constraint sets or lies within exactly one constraint set and induces a bipartition already present in that constraint tree. The rejoin step adds exactly the bridges needed to separate the constraint sets and refines the collapsed tree so that it induces every constraint tree, so the output keeps every guide-tree bipartition compatible with an unblended merge, which minimises the missing branches; hashing bipartitions gives the quadratic time. Blending can be necessary for the global optimum: for the caterpillar $(1,(2,(3,(4,(5,(6,(7,8)))))))$ and constraint trees $(1,(5,(6,7)))$, $(2,(3,(4,8)))$, the true tree interleaves the two subsets and cannot be formed by adding a single connecting edge. For consistency, with enough data the starting tree equals the true tree, its edge-deletion subsets are convex, the subset trees equal the induced true subtrees, no guide-tree edge is collapsed, and GTM returns the true tree.

## Sources

- Smirnov V, Warnow T, "Unblended disjoint tree merging using GTM improves species tree estimation" (2020), Definitions 1-3, Theorem 1 (NP-hardness), the GTM algorithm with Theorem 2, and Theorem 3 (statistical consistency), <https://doi.org/10.1186/s12864-020-6605-1>, PMCID PMC7161100.
