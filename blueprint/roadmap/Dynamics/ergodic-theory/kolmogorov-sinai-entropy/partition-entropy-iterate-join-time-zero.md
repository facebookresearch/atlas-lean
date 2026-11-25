# Entropy of the refined time-zero partition

Let $S$ be a finite alphabet with its discrete σ-algebra and $p$ a probability measure on $S$. For the Bernoulli
shift $\sigma$ on $S^{\mathbb{N}}$ with the product measure $p^{\mathbb{N}}$, every $n \ge 0$ and the
[time-zero partition](time-zero-partition.md) $\xi = \{[s] : s \in S\}$,

$$H\bigl(\xi \vee \sigma^{-1}\xi \vee \dots \vee \sigma^{-(n-1)}\xi\bigr) = n\, H(p), \qquad
H(p) = -\sum_{s} p(s) \log p(s).$$

The atoms of the refinement are the [cylinders of length $n$](iterate-join-time-zero.md), of measure
[$p(w_0) \cdots p(w_{n-1})$](infinite-pi-cylinder-word.md), and the entropy of $n$ independent letters is
[$n$ times the entropy of one](sum-neg-mul-log-prod.md).

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), proof of Proposition 4.6.
