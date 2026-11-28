# Kawarabayashi-Thorup-Yoneda coloring of 3-colorable graphs with O~(n^0.19747) colors

There is a polynomial-time algorithm that colors every $3$-colorable graph on $n$ vertices with $\widetilde{O}(n^{0.19747})$ colors, improving the previous bound $\widetilde{O}(n^{0.19996})$ of Kawarabayashi and Thorup. Its combinatorial core states: given any $3$-colorable graph with minimum degree $d > \sqrt{n}$, one can in polynomial time make progress, in Blum's sense, towards a $k$-coloring with $k = \sqrt{n/d} \cdot n^{o(1)}$; this is balanced against Chlamtac's semidefinite-programming coloring algorithm, which is used for degrees below $n^{0.605073}$.

## Proof sketch

Blum's framework reduces coloring with few colors to repeatedly making progress: finding a large independent set or a structure that shrinks the problem by a controlled amount. In the high-degree regime the algorithm exploits that every neighbourhood of a $3$-colorable graph is $2$-colorable and analyses second neighbourhoods combinatorially to make progress towards $\sqrt{n/d} \cdot n^{o(1)}$ colors. In the low-degree regime Chlamtac's algorithm, which rounds a lifted (Lasserre-hierarchy) strengthening of the Karger-Motwani-Sudan vector-coloring relaxation, is applied, and optimizing the degree threshold between the two regimes yields the exponent $0.19747$.

## Depends on

- [Vector colorings and the vector chromatic number](vector-colorings-and-vector-chromatic-number.md)

## Proof depends on

- [Karger-Motwani-Sudan coloring of 3-colorable graphs by rounding vector colorings](karger-motwani-sudan-vector-coloring-rounding.md)

## Sources

- K. Kawarabayashi, M. Thorup, H. Yoneda, "Better coloring of 3-colorable graphs", STOC (2024), arXiv:2406.00357.
- K. Kawarabayashi, M. Thorup, "Coloring 3-colorable graphs with less than n^{1/5} colors", Journal of the ACM 64 (2017).
- E. Chlamtac, "Approximation Algorithms Using Hierarchies of Semidefinite Programming Relaxations", FOCS (2007).
- D. Karger, R. Motwani, M. Sudan, "Approximate Graph Coloring by Semidefinite Programming", Journal of the ACM 45 (1998), arXiv:cs/9812008.
