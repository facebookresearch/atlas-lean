# Leaf removal to non-apparent-duplication-free gene trees via agreement subtrees

**Definitions.** A gene tree $T$ is a rooted binary tree whose leaves are genes labelled by their genomes (species) from a set $\mathcal G$, with repeated labels allowed; $L(x)$ denotes the genome set below a vertex $x$. Given a species tree $S$ on $\mathcal G$, the LCA mapping sends $x$ to the lowest vertex $M(x)$ of $S$ with $L(x) \subseteq L(M(x))$, and $x$ is a duplication if $M(x)$ equals the image of one of its children. A vertex is an apparent duplication (AD) if its two child genome sets intersect; it is a duplication for every species tree. A duplication that is not an AD is a non-apparent duplication (NAD); it signals a species triplet $\{a,b,c\}$ that $x$ splits as $ab\,|\,c$ against the species tree. $T$ is MD-consistent with $S$ if all its duplications are apparent. A weighted tree is a uniquely leaf-labelled tree with leaf weights; for a subtree $U$, the weighted tree induced by $(U,S)$ is $S$ restricted to $L(U)$ with each leaf $s$ weighted by the number of leaves of $U$ labelled $s$.

**Problems.** MINLRR asks for the fewest gene leaves of $T$ to remove so that the result is MD-consistent with $S$; MINSRR asks for the fewest species labels to remove (all their leaves at once).

**Theorem.** Suppose $T$ satisfies Constraint C: no AD vertex lies above a NAD vertex. Let $T_I$ be obtained by replacing each maximal subtree rooted at an AD vertex by its weighted induced tree. Then
1. if $W_{\max}$ is a maximum-value weighted agreement subtree of $T_I$ and $S$ (a weighted subtree of $T_I$ consistent with $S$ maximizing the total leaf weight), the subtree $T_{\max}$ of $T$ keeping exactly the leaves whose labels are in $W_{\max}$ solves MINLRR;
2. if $W_{\max}$ is a maximum agreement subtree of $T_I$ and $S$ ignoring weights, the induced $T_{\max}$ solves MINSRR.
Weighted maximum agreement subtree is solved by the usual maximum agreement subtree algorithms in the same asymptotic time. For general gene trees, iterating this step from the NAD vertices nearest the AD layer gives a correction algorithm running in $O(n^2\log n)$ time on a tree of size $n$.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Removing leaves never turns a non-duplication into a duplication, and below an AD vertex the gene tree can be collapsed to the species tree on its genome set without creating NADs, which is why AD subtrees are replaced by weighted copies of $S$. Under Constraint C the remaining NADs lie in the uniquely labelled top part, where a vertex is a NAD exactly when it contradicts $S$ on some triplet, so removing labels until the top part agrees with $S$ is an agreement-subtree problem; the weights count how many gene leaves each label removal deletes. Conversely, any MD-consistent subtree of $T$ yields a weighted agreement subtree of the same value, giving optimality.

## Sources

- K. M. Swenson, A. Doroftei, N. El-Mabrouk, "Gene tree correction for reconciliation and species tree inference", Algorithms for Molecular Biology 7:31 (2012), Definitions 1–2, problem statements, Theorem 1 with Lemmas 1–2, Corollary 1 and Theorem 2, <https://doi.org/10.1186/1748-7188-7-31>, PMCID PMC3567949.
