# Cohen: bipartite Ramanujan graphs of all degrees and sizes in polynomial time

There is a deterministic algorithm that, given $d \ge 3$ and $n$, outputs a $d$-regular bipartite Ramanujan multigraph with $n$ vertices per side in time $\mathrm{poly}(n, d)$.

## Proof sketch

Make the interlacing family argument constructive: at each step of fixing one matching edge by edge, compute (approximately, with sufficient precision) the largest roots of the two or more conditional expected polynomials and follow a branch whose largest root does not increase. The conditional expectations are computable in polynomial time via finite free convolutions and determinantal formulas, and root bounds are certified with barrier functions.

## Depends on

- [Marcus-Spielman-Srivastava: bipartite Ramanujan graphs of every degree and every size](bipartite-ramanujan-graphs-of-all-sizes.md)

## Proof depends on

- [Marcus-Spielman-Srivastava: bipartite Ramanujan graphs of every degree and every size](bipartite-ramanujan-graphs-of-all-sizes.md)

## Sources

- Michael B. Cohen, "Ramanujan graphs in polynomial time", FOCS (2016); arXiv:1604.03544.
