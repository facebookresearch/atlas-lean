# Path laws of Kingman's coalescent on a finite sample are consistent under restriction

Let $X^n$ be the
[continuous-time Markov chain path process](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md) with
[Kingman's partition rate matrix](partition-rate.md) on the partitions of $\{1, \dots, n\}$, started from the
partition into singletons. For every $k \ge 1$ and times $0 \le t_1 < \dots < t_k$, the restriction of
$(X^{n+1}_{t_1}, \dots, X^{n+1}_{t_k})$ to $\{1, \dots, n\}$ has the law of $(X^n_{t_1}, \dots, X^n_{t_k})$.

## Depends on

- [Kingman's partition rate matrix](partition-rate.md)
- [Path process of a finite continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)

## Proof depends on

- [Restriction intertwines Kingman's rate matrices](partition-rate-mul-restrict-matrix.md)
- [Finite-dimensional distributions of the path process](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md)

## Expansion

A sound expansion passes the intertwining to the matrix exponentials and applies it to each factor of
the product formula for the finite-dimensional distributions; the one-time case is
[the consistency of the time-$t$ marginals](sum-time-law-restrict.md).

## Sources

- J. F. C. Kingman, "The coalescent", Stochastic Processes and their Applications 13 (1982), 235–248, <https://doi.org/10.1016/0304-4149(82)90011-4>, Sections 1–2 (the $n$-coalescent and its restriction property).
- N. Berestycki, *Recent progress in coalescent theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática (2009), preprint <https://arxiv.org/abs/0909.3985>, Section 2.1, the paragraph on consistency before Proposition 2.1.
