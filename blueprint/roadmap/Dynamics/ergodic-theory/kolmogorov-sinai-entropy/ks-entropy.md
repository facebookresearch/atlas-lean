# Kolmogorov–Sinai entropy

Let $T : X \to X$ be a map of a probability space $(X, \mu)$. The Kolmogorov–Sinai entropy of $T$ is

$$h_\mu(T) = \sup_\xi h_\mu(T, \xi),$$

the supremum, over all [measurable partitions modulo null sets](is-measurable-partition.md)
$\xi = (C_1, \dots, C_r)$ of $X$ with finitely many atoms ($r \ge 0$), of the
[entropy of $T$ relative to $\xi$](entropy-rel.md). It takes values in $[0, \infty]$.

A partition $\xi = \{C_1, \dots, C_r\}$ turns every point $x$ into the sequence of symbols
$w_k(x) = j$ if $T^k x \in C_j$, a stationary random process when $\mu$ is an invariant probability;
$h_\mu(T, \xi)$ is the entropy per symbol of that process and $h_\mu(T)$ the largest such rate. Kolmogorov
introduced an entropy for a restricted class of systems; the definition over all finite partitions is
Sinai's (1959). It is [an invariant of isomorphism modulo null sets](ks-entropy-eq-of-is-isomorphic-mod0.md), it is computed by
[Sinai's generator theorem](ks-entropy-eq-entropy-rel-of-is-generato.md), and for the Bernoulli shift
with probability vector $p$ it equals [$-\sum_i p_i \log p_i$](ks-entropy-bernoulli-shift.md).

The planar statements of Pesin and Young in
[Entropy, dimension and Lyapunov exponents](../../smooth-dynamics/entropy-dimension-and-lyapunov-exponents/README.md)
use a real-valued entropy, which takes the value $0$ when the supremum is infinite.

## Background

- [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md):
  the entropy of a partition is the Shannon entropy of the law of the atom containing a random point
  (in nats with the natural logarithm, in bits with $\log_2$).

## Sources

- Ya. G. Sinai, *Kolmogorov–Sinai entropy*, Scholarpedia 4(3):2034 (2009), Definition 1 and §History.
- Ya. G. Sinai, *On the notion of entropy of a dynamical system*, Dokl. Akad. Nauk SSSR 124 (1959),
  768–771.
