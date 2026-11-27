# Metrics on which the work function algorithm is $k$-competitive

The work function algorithm is $k$-competitive (so the $k$-server conjecture holds) for $k = 2$ on every metric space, for every $k$ on metric spaces with exactly $k+2$ points, on the real line, and on weighted star metrics.

## Proof sketch

By the extended-cost argument it suffices to show $\sum_t \mathrm{ext}_t \le (k+1)\,\mathrm{OPT}_T + \text{const}$, that is, to find a potential, minimized when one of its free points equals the last request, that contains $k + 1$ work-function values instead of the $2k$ of the general bound. For $k = 2$ Chrobak and Larmore give such a potential with a case analysis. On the line, when all requests lie in an interval $[L, R]$ some minimizer of the duality lemma consists of copies of $L$ and $R$ only, and $\sum_{i=0}^{k} w_t(L^i R^{k-i})$ serves as the potential; Bartal and Koutsoupias treat metric spaces with $k+2$ points and weighted stars with further, more involved potentials.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Work functions and the work function algorithm](../paging-and-k-server/work-functions-and-the-work-function-algorithm.md)
- [The deterministic k-server conjecture](k-server-conjecture.md)

## Proof depends on

- [The work function algorithm is $(2k-1)$-competitive](wfa-is-2k-minus-1-competitive.md)
- [Online cost of the work function algorithm via extended costs](wfa-cost-via-extended-cost.md)

## Sources

- Yair Bartal, Elias Koutsoupias, "On the Competitive Ratio of the Work Function Algorithm for the k-Server Problem", Theoretical Computer Science 324(2-3) (2004).
- Marek Chrobak, Lawrence L. Larmore, "The Server Problem and On-Line Games", DIMACS Series in Discrete Mathematics and Theoretical Computer Science 7 (1992).
- Elias Koutsoupias, "The k-Server Problem", Computer Science Review 3(2) (2009), Section 3.3.
