# Quasipolynomial Sauer–Shelah–Perles lemma for partial classes

Let $H$ be a partial concept class on a finite domain $X$ with $\mathrm{VC}(H) = d$. Then $H$ has a disambiguation $\bar H$ of size $|\bar H| = |X|^{O(d \log |X|)}$. On the countable domain $X = \mathbb{N}$, every partial class of VC dimension $d$ has a strong disambiguation $\bar H$ whose projection to $[m]$ has size at most $(m+1)^{(d+1) \log_2 m + 2}$ for every $m$. There are partial classes of VC dimension $1$ on $m$ points all of whose disambiguations have size $m^{(\log m)^{1-o(1)}}$, so the factor $\log |X|$ in the exponent cannot be replaced by a constant.

## Proof sketch

Run the realizable one-inclusion-graph learner as a compression procedure: every realizable labelling of a finite set is recovered from a subsample of size $O(d \log |X|)$, since repeatedly the out-degree bound allows halving the number of uncovered points with $O(d)$ retained examples. The total class of all reconstructions has at most $|X|^{O(d \log |X|)}$ members and realizes every realizable sample. For $\mathbb{N}$, apply the construction consistently along the initial segments $[m]$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Disambiguations of partial concept classes](disambiguation.md)

## Proof depends on

- [VC dimension characterizes PAC learnability of partial concept classes](partial-class-pac-characterization.md)
- [Sauer bound for the growth function](../../../../../not-yet-classified/growth-function/growth-function-le-sum.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444.
