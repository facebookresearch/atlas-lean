# Bounded states theorem for the maximum parsimony distance

**Setting.** For unrooted binary phylogenetic trees $T_1, T_2$ on a taxon set $X$ and a character $\chi : X \to C$, let $\ell(T, \chi)$ be the parsimony score (minimum number of state changes on $T$ over extensions of $\chi$). The *maximum parsimony distance* is

$$d_{\mathrm{MP}}(T_1, T_2) = \max_\chi \bigl|\ell(T_1, \chi) - \ell(T_2, \chi)\bigr| .$$

A character is *convex* on $T$ if $\ell(T, \chi) = |\chi(X)| - 1$, i.e. each state class induces a connected subtree; the maximum is always attained by a character convex on one of the trees (an *optimal convex character*).

**Theorem.**
1. *(Improved bounded states theorem.)* Every pair with $d_{\mathrm{MP}}(T_1, T_2) \ge 1$ admits an optimal convex character with at most $2\, d_{\mathrm{MP}}(T_1, T_2)$ states, improving the earlier bound $7\, d_{\mathrm{MP}}(T_1, T_2) - 5$.
2. *(Lower bound.)* For every $r \ge 1$ there are binary trees $T_1, T_2$ on $n = 4r$ leaves with $d_{\mathrm{MP}}(T_1, T_2) = r$ such that some character convex on $T_1$ or $T_2$ with exactly $r + 1$ states attains the distance, while every character with fewer states gives a difference $< r$. Hence $k + 1$ states are sometimes necessary.

## Depends on

- [Fitch's algorithm](../../small-parsimony-problem/fitch.md)

## Expansion

Among optimal convex characters take one with the fewest states. A *good pair* of states could be merged without lowering the score difference, so a minimal character has none; this forbids many adjacencies between singleton-like states in the quotient structure. An adjacency theorem then bounds the number of state components that can sit on the macro-edges of the tree spanned by the remaining structure, by counting edges in trees with $k$ leaves (at most $2k-3$), and induction yields $2k$. Since convex characters on $s$ states number only polynomially many for fixed $s$, the bound shrinks the search space for computing $d_{\mathrm{MP}}$; empirically far fewer than $k+1$ states usually suffice.

## Sources

- M. Fischer, S. Kelk, S. Vazquez Alferez, "A strengthened bound on the number of states required to characterize maximum parsimony distance", *Theoretical Computer Science* 1080 (2026), 116057, Bounded States Theorem (Section 2), Improved Bounded States Theorem (Sections 2 and 4) and Proposition 1, <https://doi.org/10.1016/j.tcs.2026.116057> (preprint arXiv:2506.09888).
