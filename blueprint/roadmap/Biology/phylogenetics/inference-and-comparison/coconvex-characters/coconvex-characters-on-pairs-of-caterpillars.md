# Coconvex characters on pairs of caterpillars

**Setting.** A character on a set $X$ of $n$ species is a partition of $X$ into classes (states). It is *convex* on a phylogenetic tree with leaf set $X$ if the subtrees spanned by the different classes are pairwise vertex-disjoint, and *coconvex* on a collection of trees if it is convex on each of them. A character is *trivial* if it has at most one class of size at least $2$; trivial characters are coconvex on every collection. A *caterpillar* is a tree whose internal vertices form a path. Let $c_{n,k}$ (resp. $c_n$) be the minimum, over all pairs of $n$-leaf caterpillars, of the number of coconvex characters with exactly $k$ classes (resp. of any number of classes).

**Theorem.**

1. For $n\ge1$ and $1\le k\le\lceil n/3\rceil$, $c_{n,k} = \binom{n}{k-1}$: some pair of caterpillars shares no nontrivial $k$-class convex character, so only the trivial ones (a non-singleton class plus $k-1$ singletons) remain.
2. $c_n \ge 2^n + \big(\tfrac12 - o(1)\big)\,2^{2\lfloor n/4\rfloor}$, so any two caterpillars share exponentially many nontrivial convex characters.
3. For two caterpillars built from independent uniformly random leaf orders, the expected number of shared nontrivial convex characters is $\Theta(2^n/n^2)$.

## Expansion

Every trivial character with $k$ classes (one class plus $k-1$ singletons) is convex on every tree, which gives $c_{n,k}\ge\binom{n}{k-1}$; the content of the first statement is a pair of caterpillars sharing no other convex $k$-class character when $k\le\lceil n/3\rceil$. The lower bound on $c_n$ comes from showing that any two caterpillars share many partitions with exactly two classes of size at least $2$ and many singletons, counted by a sum of binomial coefficients in $n/4$. Since an $n$-leaf tree has at most $F_{2n-1}$ convex characters, all these counts lie between $2^n-n$ and $O(2.619^n)$.

## Sources

- E. Czabarka, S. Kelk, V. Moulton, L. A. Székely, "Coconvex characters on collections of phylogenetic trees", *Advances in Applied Mathematics* 172 (2026), 102952, Corollary 3 and Theorems 5–6, <https://doi.org/10.1016/j.aam.2025.102952> (preprint arXiv:2504.00635).
