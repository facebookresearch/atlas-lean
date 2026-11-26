# Arithmetic progressions from divergent reciprocals

Let $A\subseteq\mathbb N$ and let $u_n$ be $1/n$ for positive $n\in A$ and zero otherwise (in particular $u_0=0$, regardless of whether $0\in A$). If $\sum_n u_n$ is not summable, then for each natural $k$ there exist $a,d\in\mathbb N$ with $d>0$ and $a+id\in A$ for all $0\le i<k$. For $k=0$ the membership condition is vacuous.

## Depends on

- Restricted reciprocal series with zero convention and natural arithmetic progressions of positive step.

## Expansion

Separate the finite quantitative input from the reciprocal argument. For each fixed target length $k$, let $r_k(N)$ be the largest size of a subset of $\{1,\ldots,N\}$ with no length-$k$ arithmetic progression of positive common difference. The input is summability of the series $\sum_{m\ge0}r_k(2^m)/2^m$. The bound on reciprocal sums in a dyadic block is part of the application: translate the block $[2^m,2^{m+1})$ into $\{1,\ldots,2^m\}$ before applying the finite extremal bound.

## Proof outline

Prove the finite-interval estimate for each fixed length, then sum the dyadic block contributions to the reciprocal series under progression avoidance. Treat 0, lengths 0 and 1 separately; do not replace divergent reciprocals by positive upper density.

## Sources

- [Comparator statement: `OAI.Erdos3.manuscriptReciprocalProgressionTheorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ErdosReciprocal.lean#L31-L33)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/159.md)
- [Finite extremal number on the initial interval](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Progressions/Model.lean#L6-L16), and [the exact summability input to the reciprocal reduction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/Progressions/Results/Reciprocal.lean#L43-L90).
