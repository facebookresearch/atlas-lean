# k-interval cospeciation distance and its extremal neighborhoods

Let $T_1, T_2$ be unrooted binary phylogenetic trees on $n$ taxa with a bijection between their leaves (for example host species and their parasites, or two gene trees for the same species). Write $\varepsilon_j(A,B)$ for the number of edges on the path between leaves $A,B$ of $T_j$. The trees satisfy **$k$-interval cospeciation** ($k$-IC) if

$$\big|\varepsilon_1(A,B) - \varepsilon_2(a,b)\big| \le k \quad \text{for all pairs of leaves } A,B \text{ of } T_1 \text{ with partners } a,b \text{ in } T_2,$$

and **precise** $k$-IC if they satisfy $k$-IC but not $(k-1)$-IC; set $d(T_1,T_2) = k$. A **cherry** is a pair of leaves at path length $2$, and a **caterpillar** is a tree with exactly two cherries. The **$k$-interval neighborhood** $\mathrm{IN}_k(T)$ is the set of $n$-taxon trees $T'$ with $d(T,T') = k$.

**Theorem (metric and complexity).** $d$ is a metric on $n$-taxon trees, computable in polynomial time ($O(n^3 \log n)$ via all pairwise path lengths).

**Theorem (relation to other quantities).** If $T_1, T_2$ precisely satisfy $k$-IC, then the nearest-neighbor-interchange distance satisfies $d_{\mathrm{NNI}}(T_1,T_2) \ge k$; and the lengths (in edges) of the longest leaf-to-leaf paths of $T_1$ and $T_2$ differ by at most $k$, with the two end taxa of a longest path of $T_1$ also ending a longest path of $T_2$ when the difference equals $k$.

**Theorem (maximal distance).** Two $n$-taxon trees satisfy precise $k$-IC for some $k \le n-3$; if $d(T,T') = n-3$, at least one of $T, T'$ is a caterpillar. For a tree $T$ with $c \ge 3$ cherries,

$$|\mathrm{IN}_{n-3}(T)| = c\big((n-2)! - (n-4)!\,(c-1)\big).$$

Among trees with at least three cherries the maximal-distance neighborhood is smallest for three cherries and largest for $\lfloor n/2 \rfloor$ cherries, growing quadratically in $c$; over all $n$-taxon trees the caterpillar has the largest $(n-3)$-interval neighborhood; and for every tree the proportion of all trees lying in $\mathrm{IN}_{n-3}(T)$ tends to $0$ as $n \to \infty$.

## Expansion

Symmetry and $d(T,T) = 0$ are immediate, and the path-length metric determines an unrooted binary tree, so $d(T_1,T_2) = 0$ forces $T_1 = T_2$; the triangle inequality follows by adding the inequalities $|\varepsilon_1 - \varepsilon_2| \le x$ and $|\varepsilon_2 - \varepsilon_3| \le y$. One NNI move changes any leaf-to-leaf path length by at most $1$, which gives the NNI bound. Path lengths between leaves range from $2$ to at most $n-1$, and a pair at distance $2$ (a cherry) in one tree can be at distance at most $n-1$ in the other, which caps $d$ at $n-3$ and forces a caterpillar at the extreme. Counting $\mathrm{IN}_{n-3}(T)$ reduces to counting trees in which some cherry of $T$ becomes the pair of ends of a caterpillar spine, with inclusion–exclusion over cherries; comparison with the $(2n-5)!!$ total trees gives the vanishing proportion.

## Sources

- Jane Ivy Coons, Joseph Rusinko, "Combinatorics of k-Interval Cospeciation for Cophylogeny", arXiv (2014). Definitions in Section 2, Theorems 1–4, Lemma 1, Corollary 1, Theorems 5–8. <https://doi.org/10.48550/arXiv.1407.6605>. Published version: "A note on the path interval distance", Journal of Theoretical Biology 398 (2016), 145–149, <https://doi.org/10.1016/j.jtbi.2016.03.027>; locators above refer to the arXiv version.
