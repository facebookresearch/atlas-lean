# Entropy of the Bernoulli shift relative to the time-zero partition

Let $S$ be a finite alphabet with its discrete σ-algebra and $p$ a probability measure on $S$. For the Bernoulli
shift $\sigma$ on $S^{\mathbb{N}}$ with the product measure $p^{\mathbb{N}}$ and the
[time-zero partition](time-zero-partition.md) $\xi$,

$$h(\sigma, \xi) = H(p) = -\sum_{s \in S} p(s) \log p(s).$$

By the [entropy of the refined time-zero partition](partition-entropy-iterate-join-time-zero.md), the sequence
$\frac1n H(\xi \vee \dots \vee \sigma^{-(n-1)}\xi)$ is constant, equal to $H(p)$, for $n \ge 1$, so its limit is
$H(p)$.

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), proof of Proposition 4.6.
