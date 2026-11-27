# Kothari–Mori–O'Donnell–Witmer: SoS lower bounds for refuting any CSP

Let $P$ be a $k$-ary predicate and $3 \le t \le k$ such that $P$ supports a $(t-1)$-wise uniform distribution. Then with high probability over a random instance of $\mathrm{CSP}(P)$ with $n$ variables and $m = \Delta n$ constraints, the sum-of-squares relaxation of degree

$$
d = \widetilde{\Omega}\Bigl(\frac{n}{\Delta^{2/(t-2)}}\Bigr)
$$

fails to refute the instance even weakly: it has a degree-$d$ pseudo-expectation that satisfies every constraint. In particular, for $m \le n^{t/2 - \delta}$ SoS of degree $n^{\Omega(\delta)}$ cannot refute. The bound is strongest at $t = C(P)$, the least $\tau \in \{3, \dots, k\}$ for which $P$ supports no $\tau$-wise uniform distribution (KMOW Theorem 1.2): there polynomial-time SoS needs $\tilde\Omega(n^{C(P)/2})$ constraints, matching the refutation algorithms of Allen-O'Donnell-Witmer and Raghavendra-Rao-Schramm up to lower-order factors. For $t < C(P)$ the bound holds but is not tight; for example $4$-XOR supports both pairwise and $3$-wise uniform distributions, so $C(P) = 4$ and its threshold is $n^{2}$, not the $n^{3/2}$ given by $t = 3$.

## Proof sketch

Construct the pseudo-expectation by planting: for each constraint, sample locally from the $(t-1)$-wise uniform distribution supported on $P$, and use expansion of random hypergraphs of density $\Delta$ to show that the local distributions are consistent on all sets of at most $d$ constraints. Positivity is shown by expressing the pseudo-expectation as a global average over closures in the hypergraph, using a generalization of Schoenebeck's closure argument to $t$-wise uniformity.

## Depends on

- [Refutation of random constraint satisfaction problems](random-csp-refutation.md)
- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](lasserre-hierarchy.md)

## Proof depends on

- [Grigoriev–Schoenebeck: linear-degree SoS lower bounds for random 3-XOR and 3-SAT](schoenebeck-random-xor-sat.md)

## Sources

- P. K. Kothari, R. Mori, R. O'Donnell, D. Witmer, "Sum of squares lower bounds for refuting any CSP", STOC (2017), arXiv:1701.04521.
