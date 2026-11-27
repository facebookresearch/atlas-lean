# Minimal size of a universal tree set

**Setting.** A *split* of a taxon set $X$ ($|X|=n$) is a bipartition $A|B$ into nonempty parts; a phylogenetic $X$-tree *displays* a split if deleting some edge produces it. By the splits-equivalence theorem, a set of splits is the split set of a tree iff it contains all trivial splits and is pairwise compatible ($A\cap C$, $A\cap D$, $B\cap C$ or $B\cap D$ empty). A **universal tree set** is a collection of $X$-trees that together display every split of $X$, and the **universal incompatibility** $U(n)$ is the minimum size of such a collection.

**Theorem.** For $n=2$ or $n\ge4$ write $n=2m$ or $n=2m+1$. Then

$$U(n)=\left\lceil\frac12\binom nm\right\rceil.$$

For $n=3$ every split is trivial and the star tree displays all of them, so $U(3)=1$ (the formula would give $2$).

**Normalized incompatibility.** For a split system $S$ on $X$, the minimal number of trees needed to display $S$ divided by $U(|X|)$ lies in $(0,1]$ and allows comparing the incompatibility of split networks built on different numbers of taxa.

## Expansion

*Even $n=2m$.* By Sperner's theorem the largest antichain in the subset lattice of $X$ has size $\binom nm$, so by Dilworth's theorem the lattice splits into $\binom nm$ chains, each containing exactly one $m$-set. Mapping each subset $A$ (of size at most $m$) to the split $A|X\setminus A$ identifies the chains through $A$ and $X\setminus A$, leaving $\frac12\binom nm$ components; the splits in one component are pairwise compatible, so by the splits-equivalence theorem each component is the split set of a tree, giving a universal tree set of that size. Conversely, two distinct balanced splits ($m|m$) are never compatible, so each tree displays at most one of the $\frac12\binom nm$ balanced splits.

*Odd $n=2m+1$.* The same chain decomposition has $\binom nm$ chains, and the trees are formed by pairing chains through a perfect matching (or a matching with one unmatched vertex) in a connected vertex-transitive graph on the $m$-sets, which gives $\lceil\frac12\binom nm\rceil$ trees; Kummer's theorem shows that $\binom nm$ is odd exactly when $n+1$ is a power of $2$, which is when the ceiling matters.

## Sources

- Michael Hendriksen, Nils Kapust, "On the comparison of incompatibility of split systems across different numbers of taxa", arXiv:2004.00062 (2020), Theorem 2.1 (splits equivalence, quoted), Theorems 3.1–3.2 and Corollary 3.1 (combinatorial tools), Theorem 4.1 (main theorem) and Theorem 4.2 (Sperner, quoted), <https://doi.org/10.48550/arXiv.2004.00062>.
