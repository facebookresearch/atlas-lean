# Two-state maximum parsimony distance via convex characters and core-tree matchings

**Setting.** Let $T, T'$ be unrooted binary phylogenetic trees on a taxon set $X$ with $|X| = n$. A *character* is a partition of $X$ into states; an *extension* of $f$ to $T$ labels all vertices, and the parsimony score $l_f(T)$ is the minimum number of edges with differently labeled ends over all extensions. The *two-state maximum parsimony distance* is

$$d^2_{MP}(T, T') = \max_{f \text{ two-state}} |l_f(T) - l_f(T')|.$$

A character is *convex* on $T$ if the minimal subtrees spanning its states are vertex-disjoint; it is *covering* if these subtrees together cover all vertices of $T$ (the *natural covering extension*). The *core tree* $T_c$ is $T$ with all leaves removed; a matching $M$ in $T_c$ is *legal* if $T_c - M$ has no component consisting of a single edge joined to two edges of $M$.

**Theorem.**
1. *(Reduction to convex characters.)* There is a covering convex character $f_c$ on one of the two trees, say $T$, such that each state of $f_c$ contains at least two taxa, and its states can be recolored red and blue in polynomial time to give a two-state character $f_2$ with

$$d^2_{MP}(T, T') = |l_{f_2}(T) - l_{f_2}(T')| = l_{f_2}(T') - l_{f_2}(T).$$

Moreover $f_c$ has a unique optimal extension to $T$, its natural covering extension.
2. *(Matching correspondence.)* Covering convex characters of $T$ with at least two taxa per state are in bijection with matchings of $T_c$, and it suffices to consider legal matchings.
3. *(Counting bound.)* The maximum number of legal matchings in a tree with $m$ nodes is $O(\alpha^m)$ with $\alpha = (13384 + 8\sqrt{2793745})^{1/22} \approx 1.5895$.
4. *(Algorithm.)* $d^2_{MP}(T, T')$ can be computed in $O(\alpha^{n} \cdot \mathrm{poly}(n))$ time, improving the $O^*(\phi^n)$ bound ($\phi$ the golden ratio) that follows from item 1 alone and the trivial $O^*(2^n)$.

The same enumeration of convex characters, combined with fixed-parameter branching, computes an unrooted maximum agreement forest of $T, T'$ in $O^*(2.2973^n)$ time and a rooted one in $O^*(2.0649^n)$ time.

## Expansion

In an optimal two-state extension, cutting the mutation edges leaves a forest whose components can be taken to contain at least two taxa each; reading the components as states gives a convex character that pays exactly one mutation per cut edge on $T$, while on $T'$ the red/blue recoloring can only cost more, so the maximum is attained by such characters. A covering convex character is determined by which internal edges it cuts, and those cut edges form a matching in the core tree because every internal vertex must keep two neighbors in its own block. Counting matchings by a recursion over rooted subtrees bounds the search space, and the same recursion enumerates the candidates.

## Sources

- Steven Kelk, Ruben Meuwese and Stephan Wagner, "Convex Characters, Algorithms, and Matchings", SIAM Journal on Discrete Mathematics 38 (2024), 380–411, <https://doi.org/10.1137/21m1463999>; numbering as in arXiv:2111.12632: Theorems 2–3 (agreement forests), Definition 1, Corollary 2, Theorems 4–5, Lemma 6 and Definition 4, Theorems 6–7.
