# Quasipolynomial Sauer–Shelah–Perles lemma for partial classes

Let $H$ be a partial concept class on a finite domain $X$ with $\mathrm{VC}(H) = d$. Then $H$ has a disambiguation $\bar H$ of size $|\bar H| = |X|^{O(d \log |X|)}$. On the countable domain $X = \mathbb{N}$, every partial class of VC dimension $d$ has a strong disambiguation $\bar H$ whose projection to $[m]$ has size at most $(m+1)^{(d+1) \log_2 m + 2}$ for every $m$. There are partial classes of VC dimension $1$ on $m$ points all of whose disambiguations have size $m^{(\log m)^{1-o(1)}}$, so the factor $\log |X|$ in the exponent cannot be replaced by a constant.

## Proof sketch

Consider the online game on $X = [n]$ in which the learner predicts the labels of $1, \dots, n$ in order and is corrected only at points of the target's support where it errs. A deterministic learner that makes at most $k$ mistakes against every $h \in H$ defines a disambiguation of size at most $\binom{n}{\le k}$: each total concept is the learner's prediction sequence for one set of mistake positions. A majority vote over the family of sets shattered by the current version space (which the Sauer–Shelah–Pajor bound keeps small) makes at most $O(d \log n)$ mistakes, which gives the bound $|X|^{O(d \log |X|)}$. For $\mathbb{N}$ the same learner run along $1, 2, 3, \dots$ gives one strong disambiguation whose projections to the initial segments $[m]$ obey the stated bound.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Disambiguations of partial concept classes](disambiguation.md)

## Proof depends on

- [A partial class of VC dimension one with no finite-VC disambiguation](vc-one-partial-class-without-disambiguation.md)
- [Sauer bound for the growth function](../../../../../not-yet-classified/growth-function/growth-function-le-sum.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Theorems 11, 12 and 13 and the paragraph "Disambiguating by Majority-Votes".
