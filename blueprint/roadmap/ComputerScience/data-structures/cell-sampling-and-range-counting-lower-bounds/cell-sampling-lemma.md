# Cell-sampling lemma

Let a static cell-probe structure with $S$ cells answer every query with at most $t$ probes, and let $C$ be a uniformly random set of $\Delta$ cells, $2t \le \Delta \le S$. For every fixed query $q$, the probability that all cells probed by $q$ (on the actual input) lie in $C$ is at least $\left(\frac{\Delta - t}{S}\right)^{t} \ge \left(\frac{\Delta}{2S}\right)^{t}$. Hence some set of $\Delta$ cells resolves at least $|\mathcal{Q}| \left(\frac{\Delta}{2S}\right)^{t}$ queries: their answers are determined by the addresses and contents of the cells in $C$.

## Proof sketch

If $q$ probes $t' \le t$ distinct cells, the probability that a random $\Delta$-set contains them is $\prod_{i=0}^{t'-1} \frac{\Delta - i}{S - i} \ge \left(\frac{\Delta - t}{S}\right)^{t}$. Taking expectations over $C$ of the number of resolved queries and choosing $C$ attaining the expectation gives the second claim; a resolved query can be answered by simulating its probe sequence on $C$, which never leaves $C$.

## Depends on

- [Static cell-probe structure with space $S$ and query time $t$](static-cell-probe-structure.md)

## Sources

- Rina Panigrahy, Kunal Talwar, Udi Wieder, "Lower Bounds on Near Neighbor Search via Metric Expansion", FOCS (2010), arXiv:1005.0418.
- Kasper Green Larsen, "Higher Cell Probe Lower Bounds for Evaluating Polynomials", FOCS (2012).
