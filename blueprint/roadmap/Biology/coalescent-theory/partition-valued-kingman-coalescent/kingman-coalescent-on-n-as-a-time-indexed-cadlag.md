# Kingman's coalescent on the natural numbers

There is a process $(\Pi_t)_{t \ge 0}$ with values in the partitions of $\mathbb N = \{1, 2, \dots\}$,
unique in law, such that for every $n$ the restriction of $\Pi$ to $\{1, \dots, n\}$ is Kingman's
$n$-coalescent started from singletons, that is, has the finite-dimensional distributions of the
[path process](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md) with
[Kingman's partition rate matrix](partition-rate.md). It can be chosen so that every restriction has right-continuous
paths with left limits, and its law is invariant under finite permutations of $\mathbb N$.

## Depends on

- [Kingman's partition rate matrix](partition-rate.md)
- [Path process of a finite continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)

## Proof depends on

- [Path laws of Kingman's coalescent on a finite sample are consistent under restriction](strong-path-level-restriction-consistency-of-the.md)
- [Kolmogorov extension theorem](../../../Probability/foundations/kolmogorov-extension-theorem/kolmogorov-extension.md)

## Expansion

A sound expansion indexes the coordinates by pairs $(m, t)$ with $m \in \mathbb N$ and $t$ rational,
uses the restriction consistency in $m$ and the marginalization consistency in $t$ to apply the
Kolmogorov extension theorem, and then defines each restricted path at real times by right limits along
rational times; the limits exist because each restricted path is monotone for refinement and takes
values in a finite set. The right-limit path agrees almost surely with the coordinates at all rational
times simultaneously (a countable family), and its finite-dimensional distributions at real times are
the prescribed ones because the finite-state chain is stochastically continuous: the probability that it
jumps in $(t, t + h]$ tends to $0$ as $h \downarrow 0$. Exchangeability follows from that of the rate
matrices.

## Sources

- J. F. C. Kingman, "The coalescent", Stochastic Processes and their Applications 13 (1982), 235–248, <https://doi.org/10.1016/0304-4149(82)90011-4>, Section 4, Theorems 3 and 4.
- N. Berestycki, *Recent progress in coalescent theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática (2009), preprint <https://arxiv.org/abs/0909.3985>, Section 2.1, Proposition 2.1 and the paragraph after it.
