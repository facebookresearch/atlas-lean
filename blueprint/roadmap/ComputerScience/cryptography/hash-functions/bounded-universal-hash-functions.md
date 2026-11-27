# Bounded universal hash functions

Let $H : K \times S \to T$ be a keyed hash function with $K$ finite and nonempty, and let $\varepsilon \ge 0$. Then $H$ is an *$\varepsilon$-bounded universal hash function* ($\varepsilon$-UHF) if for all distinct $s, s' \in S$,

$$
\Pr_{k \text{ uniform on } K}[H(k, s) = H(k, s')]
= \frac{|\{k \in K : H(k, s) = H(k, s')\}|}{|K|}
\le \varepsilon.
$$

The count is over keys, not distinct functions: different keys may induce the same function. There is no finiteness requirement on $S$ or $T$.

Equivalently, a pair of distinct inputs selected at random independently of the key has collision probability at most $\varepsilon$: conditioning on the pair gives the bound, and a fixed pair is allowed. If $T$ is finite and nonempty, with $N = |T|$, the bound $(1+\alpha)/N$ for $\alpha \ge 0$ is a factor of $1+\alpha$ times the collision probability $1/N$ for independent uniform outputs.

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, [Definition 7.2 and equation (7.1)](https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_4.pdf).
