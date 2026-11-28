# Approximation and fixed-parameter algorithms for nonbinary agreement forests

Let $T_1, T_2$ be rooted phylogenetic trees (not necessarily binary) on the same taxon set $X$, $n = |X|$, each with a root leaf $\rho$ attached above the original root. For $Y \subseteq X$, $T_i|Y$ is the minimal subtree spanning $Y$ with degree-2 vertices suppressed. An **agreement forest** is a partition $\mathcal F = \{F_\rho, F_1, \dots, F_k\}$ of $X \cup \{\rho\}$ such that:

1. for each component $F$, the trees $T_1|F$ and $T_2|F$ have a common refinement;
2. the subtrees $T_i(F)$, $F \in \mathcal F$, are edge-disjoint in $T_i$ for $i = 1,2$.

A **maximum agreement forest** (MAF) has the fewest components. It is **acyclic** if the inheritance graph on components (an arc $F \to F'$ when, for some $i \in \{1,2\}$, the path in $T_i$ from the root of $T_i(F)$ to the root of $T_i(F')$ contains an edge of $T_i(F)$) is acyclic; a maximum acyclic agreement forest (MAAF) of $T_1,T_2$ has $|\mathcal F| - 1$ equal to the hybridization number $h(T_1,T_2)$ (minimum number of reticulations in a network displaying refinements of both trees).

**Theorem.**

1. Nonbinary MAF has a polynomial-time $4$-approximation.
2. Nonbinary MAF can be solved exactly in $O(4^k\,\mathrm{poly}(n))$ time, where $k$ is the number of components of a maximum agreement forest minus one.
3. If Nonbinary MAF has a $c$-approximation and Directed Feedback Vertex Set has a $d$-approximation, then Nonbinary MAAF, and hence the nonbinary hybridization number, has a $d(c+3)$-approximation. With $c = 4$ this gives a $7d$-approximation, and using the best directed feedback vertex set approximation, a polynomial-time $O(\log k \log\log k)$-approximation for nonbinary MAAF, with $k$ the optimum minus one.

## Expansion

For item 3, take any maximal agreement forest $\mathcal A$ and a maximum acyclic agreement forest $\mathcal M$. Processing the components of $\mathcal M$ bottom-up, a lowest unmarked component properly intersects at most three components of the current forest, so $\mathcal A$ can be split into an acyclic agreement forest with at most $|\mathcal A| + 3|\mathcal M|$ components; cycles in the inheritance graph are then broken by a directed feedback vertex set, multiplying by $d$. Items 1 and 2 come from an iteration that picks an internal vertex of $T_1$ all of whose children are leaves and, after some simple cases, makes at most four edge cuts in the current forest of $T_2$, at least one of which is unavoidable for every maximum agreement forest, giving both a bounded-search-tree algorithm with branching factor $4$ and, by cutting all candidate edges, a $4$-approximation.

## Sources

- Leo van Iersel, Steven Kelk, Nela Lekić, Leen Stougie, "Approximation algorithms for nonbinary agreement forests", arXiv (2012); SIAM Journal on Discrete Mathematics (2014). Section 2 (Theorems 2.1–2.3, Corollaries 2.4–2.5), Section 3 (Theorem 3.4), Section 4. <https://doi.org/10.48550/arXiv.1210.3211>. Published version: SIAM Journal on Discrete Mathematics 28(1) (2014), 49–66, <https://doi.org/10.1137/120903567>; locators above refer to the arXiv version.
