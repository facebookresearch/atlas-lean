# Game characterizations of universal and difference-universal hashing

Let $H_k : M \to T$ be a keyed family with a uniform key from a finite key set. (a) $H$ is $\varepsilon$-universal (every distinct pair collides with probability at most $\varepsilon$) iff every adversary, given no information about the key and outputting two distinct messages, wins the collision game with probability at most $\varepsilon$. (b) For $T$ an abelian group, $H$ is $\varepsilon$-difference-universal ($\Pr_k[H_k(m) - H_k(m') = \delta] \le \varepsilon$ for all $m \ne m'$ and $\delta$) iff every adversary outputting $(m, m', \delta)$ wins the difference game with probability at most $\varepsilon$. When the messages can be enumerated, a maximizing pair can be found by exhaustive search independently of the key.

## Proof sketch

An adversary's output is independent of the key, so its winning probability is an average of pairwise collision (or difference) probabilities, which is at most the maximum; conversely the adversary outputting a maximizing pair attains it.

## Depends on

- [Universal hash family](../../../data-structures/hashing/universal-hashing/is-universal.md)
- [Bounded universal hash functions](../../hash-functions/bounded-universal-hash-functions.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
