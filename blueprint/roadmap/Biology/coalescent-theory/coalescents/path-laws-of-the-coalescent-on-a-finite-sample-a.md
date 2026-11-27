# Path laws of the Λ-coalescent on a finite sample are consistent under restriction

Let $\Lambda$ be a finite measure on $[0, 1]$ and let $X^n$ be the
[continuous-time Markov chain path process](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md) with the
[Λ-coalescent rate matrix](the-coalescent-rate-matrix-on-partitions-of-a-fi.md) $Q^\Lambda_n$ started from the partition of $\{1, \dots, n\}$ into
singletons. Then $\mathbb P(X^n_t = \pi) = \exp(t Q^\Lambda_n)(\bot, \pi)$, its finite-dimensional
distributions are products of the matrices $\exp((t_{i+1} - t_i) Q^\Lambda_n)$, and the process
obtained by restricting $X^{n+1}$ to $\{1, \dots, n\}$ has the same finite-dimensional distributions as
$X^n$.

## Depends on

- [The Λ-coalescent rate matrix on partitions of a finite sample](the-coalescent-rate-matrix-on-partitions-of-a-fi.md)
- [Path process of a finite continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)

## Proof depends on

- [The Λ-coalescent rate matrix on partitions of a finite sample](the-coalescent-rate-matrix-on-partitions-of-a-fi.md)
- [Finite-dimensional distributions of the path process](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md)

## Expansion

A sound expansion passes the intertwining $Q^\Lambda_{n+1} R = R\, Q^\Lambda_n$ to the matrix exponentials,
$\exp(t Q^\Lambda_{n+1}) R = R \exp(t Q^\Lambda_n)$, and applies it factor by factor in the product formula
for the finite-dimensional distributions (Dynkin's lumpability criterion for a deterministic
function of a Markov chain).

## Sources

- J. Pitman, "Coalescents with multiple collisions", Annals of Probability 27 (1999), 1870–1902, <https://doi.org/10.1214/aop/1022874819>.
- N. Berestycki, *Recent progress in coalescent theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática (2009), preprint <https://arxiv.org/abs/0909.3985>, Section 3.1, Definition 3.1 (consistency of the family of $n$-coalescents).
