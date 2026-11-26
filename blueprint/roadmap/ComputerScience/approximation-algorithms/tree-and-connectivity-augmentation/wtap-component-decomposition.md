# Approximate decomposition of WTAP solutions into thin components (Traub-Zenklusen)

For every $\varepsilon > 0$ there is a family $\mathcal{K}_\varepsilon$ of link sets of a shadow-complete WTAP instance, of super-constant size in general, with the following two properties.

(i) For every current up-link set $U$, a component $C \in \mathcal{K}_\varepsilon$ minimizing $w(C)/w(\mathrm{Drop}_U(C))$ can be found in polynomial time for fixed $\varepsilon$, by dynamic programming over the tree.

(ii) For every WTAP solution $F$ there are components $C_1,\dots,C_q \in \mathcal{K}_\varepsilon$ with $\sum_{j}w(C_j) \le (1+\varepsilon)\,w(F)$ and $\bigcup_j\mathrm{Drop}_U(C_j)=U$.

## Proof sketch

Thin components are link sets whose induced structure along the tree is covered by boundedly many root paths, which makes the best ratio computable by a dynamic program that guesses the boundary at each vertex. For (ii), split an optimal solution by cutting the tree at a sparse set of vertices chosen by a random shift, duplicating the few links that cross the cut points; the expected duplication costs an $\varepsilon$ fraction of $w(F)$, and each piece is thin.

## Depends on

- [Relative greedy algorithms for weighted tree augmentation](relative-greedy-augmentation.md)

## Proof depends on

- [Relative greedy algorithms for weighted tree augmentation](relative-greedy-augmentation.md)

## Sources

- Vera Traub, Rico Zenklusen, "A Better-Than-2 Approximation for Weighted Tree Augmentation", FOCS (2021), arXiv:2104.07114.
