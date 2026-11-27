# Multi-labeled tree dissimilarity via maximum common trees

**Multi-labeled trees.** A multi-labeled tree is a rooted tree $T$ in which each non-root vertex $v$ carries a set $L_v$ of labels from a universe $L$, with $L_u\cap L_v = \varnothing$ for $u\neq v$; $L(T) = \bigcup_v L_v$. A *clonal tree* of tumour evolution is the special case where the root (normal cells) has no labels and every other vertex (a clone) has a non-empty set of mutations first appearing there; disjointness encodes the infinite sites assumption.

**Edit operations.**

1. *Delete a label* from some $L_v$.
2. *Delete an unlabeled leaf.*
3. *Expand a vertex*: replace $v$ by a parent–child pair $v_1\to v_2$, with $v_1$ taking $v$'s parent, $v_2$ taking $v$'s children, and $L_v$ split between $L_{v_1}$ and $L_{v_2}$.

A *common tree* of $T_1$ and $T_2$ is any multi-labeled tree reachable from both by these operations; a *maximum common tree* has the most labels. The **multi-labeled tree dissimilarity** is

$$\mathrm{MLTD}(T_1, T_2) = |L(T_1)| + |L(T_2)| - 2\,|L(T^\ast)|,$$

where $T^\ast$ is a maximum common tree: the total number of labels deleted to reach it. Vertex expansion is free, so trees differing only in granularity (one clone split into a chain) have dissimilarity $0$.

**Not a metric.** With $L = \{A, B\}$ and an unlabeled root in each tree, let $T_1$ be the path root $\to \{A\} \to \{B\}$, $T_2$ the path root $\to \{B\} \to \{A\}$, and $T_3$ the path root $\to \{A, B\}$. Then $\mathrm{MLTD}(T_1, T_3) = \mathrm{MLTD}(T_2, T_3) = 0$ but $\mathrm{MLTD}(T_1, T_2) = 2$, violating the triangle inequality.

**Polynomial-time computation.** A maximum common tree, and hence MLTD, can be computed in time polynomial in $|V(T_1)|$, $|V(T_2)|$ and the label counts. For vertices $a\in V(T_1)$, $b\in V(T_2)$ let $G(a,b)$ be the size of a maximum common tree of the subtrees rooted at $a$ and $b$, and let $G'(a,b)$ be the size of a maximum common tree of these subtrees, excluding the labels of $a$ and $b$, among those in which $a$ and $b$ are mapped to the same branching vertex of the common tree. Then, with children $a_1,\dots,a_n$ of $a$ and $b_1,\dots,b_m$ of $b$,

$$G'(a,b) = \max_N \sum_{(x,y)\in N} G(x,y),$$

the maximum over bijections $N$ between equal-size subsets of the two child sets, a maximum-weight bipartite matching, and

$$G(a,b) = \max_{x \in T_1(a),\ y \in T_2(b)} \big[G'(x,y) + D(a,b,x,y)\big],$$

where $T_i(v)$ is the vertex set of the subtree rooted at $v$ and $D(a,b,x,y)$ is the optimum of the set alignment problem for the label sequences of the downward paths $a \to x$ and $b \to y$. (The matching recurrence alone, applied to every pair, is false: for $T_1$ = $a \to a_1 \to$ leaves $\{X\}, \{Y\}$ and $T_2$ = $b \to$ leaves $\{X\}, \{Y\}$, expanding $b$ gives a common tree with two labels, which a matching of the children of $a$ and $b$ cannot reach.)

## Expansion

Because deletions are allowed only on labels and on unlabeled leaves, the branching structure of a common tree must embed in both input trees, with single-child chains of vertices compressible by expansion. This rigidity is what makes the problem tractable, in contrast to unordered labeled-tree edit distance with arbitrary vertex deletions, which is MAX SNP-hard. In the clonal-tree application, MLTD is normalised and used to compare trees inferred by different tumour-phylogeny methods with each other or with ground truth.

## Depends on

- [Set alignment problem for label-ordered paths](set-alignment-problem-for-label-ordered-paths.md)

## Sources

- N. Karpov, S. Malikic, M. K. Rahman, S. C. Sahinalp, *A multi-labeled tree dissimilarity measure for comparing "clonal trees" of tumor progression*, Algorithms for Molecular Biology 14 (2019), 17, sections "Definitions" (subsections "Multi-labeled tree" and "MLTD measure between two multi-labeled trees") and "Computing a maximum common tree in the general case" (Theorem 1). <https://doi.org/10.1186/s13015-019-0152-9> (PMCID: PMC6661107)
