# Odd-stride double hashing in power-of-two tables

For a table of $m = 2^M$ slots and hash functions $h_1, h_2 : [U] \to [2^M]$, the *odd-stride double hashing* probe sequence of key $u$ is

$$
\pi_u(i) = \left(h_1(u) + i \cdot (2 h_2(u) + 1)\right) \bmod 2^M, \qquad i = 0, 1, \dots, 2^M - 1 .
$$

Because the stride $2h_2(u)+1$ is odd, it is invertible modulo $2^M$ and $\pi_u$ is a permutation of $[2^M]$, so the probe sequence visits every slot.

## Depends on

- [Open-addressing hash table](../../open-addressing/open-addressing.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- J. P. Schmidt and A. Siegel, "The Analysis of Closed Hashing under Limited Randomness", Proceedings of the 22nd ACM Symposium on Theory of Computing (STOC), 1990.
