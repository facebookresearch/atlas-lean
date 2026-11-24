# Marked items in a uniform random sample

Let $N, K, n$ be integers with $0 \le K \le N$ and $0 \le n \le N$, let $M$ be a set of $K$ marked items among $N$ items, and let
$S$ be uniformly distributed on the nonempty set of $n$-element subsets of the items. Then the number $\lvert S \cap M\rvert$ of
marked items in the sample has the hypergeometric distribution:

$$P(\lvert S \cap M\rvert = k) = \binom{K}{k}\binom{N - K}{n - k}\Big/\binom{N}{n} \qquad \text{for } \max(0, n - N + K) \le k \le \min(n, K),$$

and $P(\lvert S \cap M\rvert = k) = 0$ for every other $k \in \mathbb{N}$, since each of the $\binom{N}{n}$ samples is equally likely and,
for $k$ in that range, $\binom{K}{k}\binom{N - K}{n - k}$ of them contain exactly $k$ marked items.

## Depends on

- [Hypergeometric distribution](hypergeometric.md)

## Proof depends on

## Sources

- C. M. Grinstead and J. L. Snell, *Introduction to Probability*, 2nd revised edition, American Mathematical Society, Section 5.1, the hypergeometric distribution (p. 193), <https://math.dartmouth.edu/~prob/prob/prob.pdf>.
