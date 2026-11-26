# Kothari–Mori–O'Donnell–Witmer: SoS lower bounds for refuting any CSP

Let $P$ be a $k$-ary predicate that supports a $(t-1)$-wise uniform distribution, $3 \le t \le k$. Then with high probability over a random instance of $\mathrm{CSP}(P)$ with $n$ variables and $m = \Delta n$ constraints, the sum-of-squares relaxation of degree

$$
d = \widetilde{\Omega}\Bigl(\frac{n}{\Delta^{2/(t-2)}}\Bigr)
$$

fails to strongly refute the instance: it has a degree-$d$ pseudo-expectation that satisfies every constraint. In particular, for $m \le n^{t/2 - \delta}$ polynomial-degree SoS cannot refute, which matches the refutation threshold up to the degree trade-off.

## Proof sketch

Construct the pseudo-expectation by planting: for each constraint, sample locally from the $(t-1)$-wise uniform distribution supported on $P$, and use expansion of random hypergraphs of density $\Delta$ to show that the local distributions are consistent on all sets of at most $d$ constraints. Positivity is shown by expressing the pseudo-expectation as a global average over closures in the hypergraph, using a generalization of Schoenebeck's closure argument to $t$-wise uniformity.

## Depends on

- [Grigoriev–Schoenebeck: linear-degree SoS lower bounds for random 3-XOR and 3-SAT](schoenebeck-random-xor-sat.md)

## Proof depends on

- [Grigoriev–Schoenebeck: linear-degree SoS lower bounds for random 3-XOR and 3-SAT](schoenebeck-random-xor-sat.md)

## Sources

- P. K. Kothari, R. Mori, R. O'Donnell, D. Witmer, "Sum of squares lower bounds for refuting any CSP", STOC (2017), arXiv:1701.04521.
