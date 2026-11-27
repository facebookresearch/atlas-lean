# Truthful online mechanism for unit-demand agents from price sampling

In the unknown single-value unit-demand setting, each agent $l \in L$ has a private value $v_l \ge 0$ for any item in its acceptable set (its neighborhood in $G \subseteq L \times R$), agents arrive in an arbitrary fixed order, and the Price Sampling Algorithm is run on reported values with each matched agent paying the price of its item. For every arrival order this mechanism is ex-post individually rational and ex-post dominant-strategy truthful (no degree bound needed), assuming nonnegative values for the other agents; under truthful reports, well-behaved values (distinct agents with equal value have value $0$) uniformly random order and at least two agents ($|L| \ge 2$), if every agent has at most $d$ acceptable items, its expected social welfare is at least a $1/(4d)$ fraction of the optimal welfare.

## Proof sketch

Sampled agents receive nothing regardless of their reports, so their reports only set prices and they cannot gain. A later agent faces prices fixed by others' reports and receives its cheapest acceptable item priced below its report, paying that price, which is the best outcome available to it whatever it reports. Welfare is the matched weight, bounded by the Price Sampling guarantee, which needs $|L| \ge 2$: with a single agent the sample of $\lceil 1/2 \rceil = 1$ arrival contains it, so it receives nothing while the optimal welfare is its value.

## Depends on

- [Dominant-strategy incentive compatibility](../../../GameTheory/mechanism-design/revelation-principle/is-dominant-strategy-incentive-compatibl.md)
- [Matroid secretary problem](matroid-secretary-problem.md)

## Proof depends on

- [Price Sampling Algorithm: 4d-competitive secretary on transversal matroids](transversal-price-sampling.md)

## Sources

- Moshe Babaioff, Nicole Immorlica and Robert Kleinberg, "Matroids, Secretary Problems, and Online Mechanisms", Proceedings of the 18th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2007, Section 2 (well-behaved inputs) and Section 4 (Price Sampling Algorithm, Claim 2, Theorems 4.1 and 4.2).
