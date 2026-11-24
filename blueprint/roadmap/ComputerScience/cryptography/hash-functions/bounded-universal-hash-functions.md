# Bounded universal hash functions

Let $H : K \times S \to T$ be a keyed hash function with $K$ finite and nonempty, and let $\varepsilon \ge 0$. Then $H$ is an *$\varepsilon$-bounded universal hash function* ($\varepsilon$-UHF) if for all distinct $s, s' \in S$,

$$\Pr_k[H(k, s) = H(k, s')] \le \varepsilon,$$


where $k$ is uniformly distributed over $K$. Equivalently, no adversary, even a computationally unbounded one, that outputs two distinct inputs without seeing the key finds a collision for a uniformly random key with probability greater than $\varepsilon$. When $T$ is finite, with $N = |T|$ and $\alpha \ge 0$, a $(1 + \alpha)/N$-UHF is one whose collision probability exceeds the value $1/N$ of a uniformly random function by at most the factor $1 + \alpha$.

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Definition 7.2 and the characterization (7.1)
