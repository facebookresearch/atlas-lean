# Held–Karp dynamic program for the traveling salesman problem

For $n \ge 2$ cities $\{1, \dots, n\}$ with arbitrary costs $d(i, j)$, let $C(S, j)$ for $1 \in S$, $j \in S \setminus \{1\}$ be the minimum cost of a path that starts at $1$, visits exactly the cities of $S$, and ends at $j$. Then $C(\{1, j\}, j) = d(1, j)$, for $|S| \ge 3$ we have $C(S, j) = \min_{i \in S \setminus \{1, j\}} C(S \setminus \{j\}, i) + d(i, j)$, and the optimal tour cost is $\min_{j \in \{2, \dots, n\}} C(\{1, \dots, n\}, j) + d(j, 1)$. The dynamic program runs in $O(2^n n^2)$ time and $O(2^n n)$ space.

## Sources

- D. Eppstein, *Graph Algorithms* lecture notes, UC Irvine CS 163/265, "The traveling salesperson problem", <https://www.ics.uci.edu/~eppstein/163/lecture5b.pdf>
- M. Held and R. M. Karp, "A dynamic programming approach to sequencing problems", *Journal of the Society for Industrial and Applied Mathematics* 10(1):196–210, 1962
