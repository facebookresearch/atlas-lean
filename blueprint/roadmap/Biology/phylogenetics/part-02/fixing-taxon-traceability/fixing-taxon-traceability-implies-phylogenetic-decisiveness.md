# Fixing taxon traceability implies phylogenetic decisiveness

**Setting.** Let $X$ be a set of $n$ taxa and $\mathcal S = \{Y_1,\dots,Y_k\}$ a collection of subsets of $X$ (the taxon sets of the available loci). $\mathcal S$ is **phylogenetically decisive** if for every binary phylogenetic $X$-tree $T$, the restrictions $T|_{Y_1},\dots,T|_{Y_k}$ determine $T$ uniquely. By the four-way partition property, this holds if and only if for every partition $X = X_1|X_2|X_3|X_4$ into four non-empty blocks some $Y_j$ contains one taxon from each block. A $c$-subset $C \subseteq X$ is a **cross $c$-tuple** if $C \not\subseteq Y_j$ for all $j$; cross 4-tuples are **cross quadruples**.

A taxon $x \notin C$ is a **fixing taxon** of the cross $c$-tuple $C = \{x_1,\dots,x_c\}$ if each of the $c$ sets $(C\setminus\{x_i\})\cup\{x\}$ is contained in some $Y_j$. A cross $c$-tuple is **fixing-taxon resolvable** if there is $x \notin C$ such that each set $C_i = (C\setminus\{x_i\})\cup\{x\}$ is either not a cross tuple, has a fixing taxon, or is reached at the end of a chain of cross tuples $C'_1,\dots,C'_l = C_i$ in which $C'_1$ has a fixing taxon and each later tuple has a fixing taxon once the earlier ones are counted as resolved. $\mathcal S$ is **fixing taxon ($c$-)traceable** if, resolving tuples in this way, every cross $c$-tuple is eventually resolved.

**Theorem.**

1. (No cross quadruples.) If $\mathcal S$ has no cross quadruple, it is phylogenetically decisive.
2. (Fixing taxa resolve quadruples.) If $n \ge 5$ and $x$ is a fixing taxon of the cross quadruple $\{a,b,c,d\}$, then any assignment of compatible trees $T_1,\dots,T_k$ on $Y_1,\dots,Y_k$ forces the same resolution of $\{a,b,c,d\}$ in every supertree.
3. (Main theorem.) Every fixing-taxon-traceable collection $\mathcal S$ (with $c = 4$) is phylogenetically decisive.
4. (Algorithm.) Whether $\mathcal S$ is fixing taxon $c$-traceable can be decided in $O(n^c\max\{k,n^2\})$ steps, which is polynomial when $k$ is polynomial in $n$.
5. (Extremal counts.) If at least $\binom nc - n + c$ of the $c$-subsets of $X$ are covered by elements of $\mathcal S$, then $\mathcal S$ is fixing taxon $c$-traceable. Every fixing-taxon-traceable collection of $c$-tuples has at least $\binom{n-1}{c-1}$ elements, and this is attained. For $n \ge 6$, the minimal number $\hat k(n)$ of quadruples in a phylogenetically decisive collection satisfies

$$\left\lceil \tfrac14\tbinom n3 \right\rceil + 2 \;\le\; \hat k(n) \;\le\; \tbinom{n-1}{3} - 1 .$$

6. (Not equivalent.) For $n \ge 6$ there is a phylogenetically decisive collection with $\binom n4 - 3n + 13$ quadruples that is not fixing taxon traceable. Below $\lceil\frac14\binom n3\rceil + 2$ quadruples, and from $\binom n4 - n + 4$ quadruples on, the two properties coincide.

## Expansion

If $x$ fixes $\{a,b,c,d\}$, the four quadruples obtained by swapping $x$ for one of $a,b,c,d$ are each displayed by some input tree, so their resolutions are fixed in any supertree. A case check on five taxa shows that the four quartets on $\{a,b,c,d,x\}$ containing $x$ determine the quartet on $\{a,b,c,d\}$. Resolved quadruples can then be used as if they were covered, which justifies the chains in the traceability definition. Induction over the resolution order shows that all quadruples are determined, and quartet-determined trees are unique, which proves decisiveness. The algorithm explores the $(c-1)$-overlap graph on $\binom Xc$, coloring cross tuples and propagating resolutions; connectivity of this graph gives the $\binom{n-1}{c-1}$ bound.

## Sources

- Mareike Fischer, Janne Pott, "Perfect taxon sampling and fixing taxon traceability: Introducing a class of phylogenetically decisive collections of taxon sets", arXiv (2012). Section 2 (Definitions 2.1–2.2, Theorems 2.3–2.4), Section 3: Proposition 3.1, Definition 3.2, Proposition 3.4, Definition 3.7, Theorem 3.9, Proposition 3.14, Theorems 3.15–3.16, Corollary 3.18, Theorem 3.20, Corollary 3.21, Theorem 3.22. <https://doi.org/10.48550/arXiv.1206.3472>. Published version: Bulletin of Mathematical Biology 87(7) (2025), article 94, <https://doi.org/10.1007/s11538-025-01457-7>; locators above refer to the arXiv version.
