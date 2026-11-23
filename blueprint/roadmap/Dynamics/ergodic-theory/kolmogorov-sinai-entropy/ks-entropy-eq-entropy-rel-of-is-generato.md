# Sinai's generator theorem

Let $T$ be an invertible measure-preserving transformation of a probability space $(X, \mathcal{B}, \mu)$ ($T$ is
measurable with measurable inverse), and let $\xi = (C_1, \dots, C_r)$ be a
[measurable partition modulo null sets](is-measurable-partition.md) which is a *generator*: the smallest
σ-algebra containing all the sets $T^n C_j$, $n \in \mathbb{Z}$, $1 \le j \le r$, is $\mathcal{B}$ modulo
$\mu$-null sets. Then

$$h_\mu(T) = h_\mu(T, \xi).$$

The theorem reduces the supremum over all partitions in the definition of
[Kolmogorov–Sinai entropy](ks-entropy.md) to a single computation. Kolmogorov proved it for Bernoulli
partitions; Sinai proved the general case in 1959, through an inequality between conditional entropies
that is an equality in the Bernoulli case. Here the integer powers of $T$ are the iterates of $T$ and of
$T^{-1}$, and "modulo $\mu$" means that every measurable set is $\mu$-almost everywhere equal to a set of the
generated σ-algebra. Its noninvertible form uses
[strong generators](ks-entropy-eq-entropy-rel-of-is-strong-g.md).

## Sources

- Ya. G. Sinai, *Kolmogorov–Sinai entropy*, Scholarpedia 4(3):2034 (2009), Definition 2 and Theorem 1, with
  the account of its proof.
- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), Definition 4.4 and Theorem 4.4 (Sinai's Generator Theorem).
