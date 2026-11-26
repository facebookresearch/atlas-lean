# Lower bound for the entropy of a Bernoulli shift

Let $S$ be a finite alphabet with its discrete σ-algebra and $p$ a probability vector on $S$. The
Kolmogorov–Sinai entropy of the Bernoulli shift with distribution $p$ satisfies

$$h(\sigma) \ge H(p) = -\sum_{s \in S} p(s) \log p(s).$$

In particular a Bernoulli shift whose distribution is not a point mass has positive entropy, which is how
entropy separates "probabilistic" systems from those of entropy zero.

The bound comes from a single partition: the [time-zero partition](time-zero-partition.md) has
[relative entropy exactly $H(p)$](entropy-rel-time-zero.md), and a relative entropy is
[at most the Kolmogorov–Sinai entropy](entropy-rel-le-ks-entropy.md). The reverse inequality, and with it the
formula [$h(\sigma) = H(p)$](ks-entropy-bernoulli-shift.md), needs Sinai's generator theorem.

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), Proposition 4.6 and its proof (the computation
  $H_\mu(\alpha_0^{n-1}) = n H(p)$ for the partition $\alpha$ into 1-cylinders).
