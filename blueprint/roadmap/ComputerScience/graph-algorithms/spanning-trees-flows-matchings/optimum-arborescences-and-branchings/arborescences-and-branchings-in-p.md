# Minimum-cost arborescences and optimum branchings are in P

With arc weights encoded in binary, the decision versions of the minimum-cost rooted spanning arborescence problem ("is there a spanning in-arborescence rooted at $r$ of cost at most $K$?") and of the maximum-weight branching problem are in $\mathrm{P}$, and the optimal objects are computable in polynomial time on multi-tape Turing machines. In the contraction implementation that only adds cycle costs, after $i$ contraction rounds every table entry satisfies $|c_i(u, v)| \le (n + 1)^i M_0$, where $M_0$ bounds the input costs, so every intermediate number has bit length $O(L^2)$ in the input length $L$.

## Proof sketch

At most $n$ contraction rounds, each polynomial in the table size; the magnitude bound follows because each round adds at most $n$ existing entries.

## Depends on

- [The Chu-Liu/Edmonds algorithm](chu-liu-edmonds-algorithm.md)
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Correctness and optimality of Chu-Liu/Edmonds](chu-liu-edmonds-correctness.md)
- [Optimum branchings by the super-root reduction](optimum-branching-reduction.md)

## Sources

- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
- R. E. Tarjan, "Finding Optimum Branchings", Networks 7(1), 1977.
