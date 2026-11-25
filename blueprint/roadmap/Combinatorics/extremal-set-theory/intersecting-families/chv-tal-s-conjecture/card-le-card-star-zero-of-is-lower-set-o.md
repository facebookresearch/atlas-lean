# Chvátal's theorem for shifted down-sets

Let $\mathcal F$ be a finite family of finite
sets of natural numbers that is closed under taking subsets and under shifting, that is,
replacing an element $j$ of a member by a smaller natural number $i$ not in that member gives
another member. Then every intersecting subfamily of $\mathcal F$ (any two members, equal or not,
meet) has at most as many members as the star $\{A \in \mathcal F : 0 \in A\}$.

The proof compresses the intersecting family at the largest element $m$ of the ground set and
splits it by whether its members contain $m$; induction on the ground set applies to both parts.

## Sources

- B. Alexeev, D. Mixon, and W. Sawin, The independence and clique cover numbers of the squarefree graph, arXiv:2507.01928 (2025), https://arxiv.org/abs/2507.01928, Section 1.1, Proposition 3, where the result is attributed to V. Chvátal, Intersecting families of edges in hypergraphs having the hereditary property, Hypergraph Seminar, Springer (1974), 61-66. There the ground set is $\{1, \dots, k\}$, the star is that of $1$, and the family is closed under passing to any set that injects into a member by a map $f$ with $x \le f(x)$, which is equivalent to closure under subsets and shifts.
