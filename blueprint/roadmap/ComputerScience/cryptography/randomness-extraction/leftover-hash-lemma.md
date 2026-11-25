# Leftover hash lemma

Let $H : K \times S \to T$ be a keyed hash with finite $K$, $S$, $T$ and $N = |T|$, which is a $(1+\alpha)/N$-universal hash function: for all $s \ne s'$, $\Pr_k[H(k, s) = H(k, s')] \le (1 + \alpha)/N$. Let $k, s_1, \dots, s_m$ be mutually independent random variables with $k$ uniform on $K$ and each $s_i$ of guessing probability at most $\gamma$. Then the statistical distance $\delta$ between $(k, H(k, s_1), \dots, H(k, s_m))$ and the uniform distribution on $K \times T^m$ satisfies

$$\delta \le \frac{m}{2}\sqrt{N\gamma + \alpha}.$$


## Depends on

- [Bounded universal hash functions](../hash-functions/bounded-universal-hash-functions.md)
- [Guessing probability, min-entropy and collision probability](guessing-probability-min-entropy-and-collision.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 8.11
- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A pseudorandom generator from any one-way function", *SIAM Journal on Computing* 28(4):1364–1396, 1999, Lemma 4.8 (the hashing lemma, in Rényi-entropy form)
