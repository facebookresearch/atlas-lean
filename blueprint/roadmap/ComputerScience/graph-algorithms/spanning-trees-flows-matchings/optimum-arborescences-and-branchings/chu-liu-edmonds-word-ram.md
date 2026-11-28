# Chu-Liu/Edmonds runs in O(mn) time

In the unit-cost model, the contraction algorithm of Chu-Liu and Edmonds computes a minimum-cost spanning in-arborescence rooted at a given vertex $r$ of a digraph with $n$ vertices, $m$ arcs and arc costs, when one exists, in $O(mn)$ time: each contraction step takes $O(m)$ time and reduces the number of vertices by at least one.

## Proof sketch

There are at most $n - 1$ contraction steps, each of which selects a cheapest outgoing arc at every vertex other than $r$, finds a cycle among the selected arcs and contracts it with reduced costs in $O(m)$ time, so the total is $O(mn)$; correctness is the linked correctness page.

Word-RAM form (derived; no cited source states it): there are absolute constants $C$ and $c$ and a deterministic word-RAM program that, given an $n$-vertex digraph with integer arc costs of absolute value at most $M$ as an adjacency and cost matrix and a root $r$, computes a minimum-cost spanning in-arborescence rooted at $r$ (or reports that none exists) within $C (n+1)^3$ instructions at every word size $w \ge c \log_2((n+1)(M+1))$, and the same bound holds for minimum-cost out-arborescences and for maximum-weight branchings through the super-root reduction. Materialize the adjacency and cost table of each contraction level as an $n \times n$ array with cycle masks and best entry and exit tables; each of at most $n$ levels costs $O(n^2)$ instructions, which is the $O(mn)$ bound of the contraction algorithm with $m \le n^2$. Every stored value is an index below $(n+1)^2$ or a cost or reduced cost, and this implementation keeps every value in one word once $4(n+1)M + 32(n+1)^2 < 2^w$. With $N = (n+1)(M+1) \ge 2$ the left side is at most $36N^2 < N^8$, so $c = 8$ suffices.

Faster implementations: Tarjan's implementation of Edmonds' algorithm runs in $O(m \log n)$ time and, for dense graphs, in $O(n^2)$ time.

## Depends on

- [The Chu-Liu/Edmonds algorithm](chu-liu-edmonds-algorithm.md)
- [Spanning arborescences and branchings](spanning-arborescences-and-branchings.md)

## Proof depends on

- [Correctness and optimality of Chu-Liu/Edmonds](chu-liu-edmonds-correctness.md)
- [Optimum branchings by the super-root reduction](optimum-branching-reduction.md)

## Sources

- R. E. Tarjan, "Finding Optimum Branchings", Networks 7(1), 1977.
- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
- A. Gupta, Lecture 2: "Min-Cost Arborescences, and LP-based Methods", 15-850 Advanced Algorithms lecture notes, Carnegie Mellon University, Fall 2018.
