# Luby–Rackoff theorem

For a function $f : \{0,1\}^n \to \{0,1\}^n$, the Feistel round maps $(L, R)$ to $(R, L \oplus f(R))$; it is a permutation of $\{0,1\}^{2n}$ for every $f$. Let $F$ be a pseudorandom function on $X = \{0,1\}^n$ and $N = 2^n$. For every adversary $A$ making at most $Q$ queries to the three-round Feistel network with independent keys and round functions $F(k_i, \cdot)$, there is a PRF adversary $B$ with

$$\mathrm{Adv}^{\mathrm{PRP}}[A] \le 3\cdot \mathrm{Adv}^{\mathrm{PRF}}[B, F] + \frac{Q^2}{N} + \frac{Q^2}{2N^2}.$$

Consequently, for a family indexed by a security parameter in which $F$ is a secure PRF and $N$ is superpolynomial, the three-round network is a secure pseudorandom permutation on $2n$-bit blocks.

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [PRP advantage](../pseudorandom-permutations/prp-advantage.md)

## Proof depends on

- [Switching lemma for distinguishers with uniform coins, birthday form](../pseudorandom-permutations/abs-prf-rand-sub-prp-rand-le-birthday.md)
- [Lazy random function](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/lazy-rf.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Feistel round permutation and three-round bijectivity (existing formal statements; page pending) (statement prerequisite; formal statement exists, page pending)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 4.9
- M. Luby and C. Rackoff, "How to construct pseudorandom permutations from pseudorandom functions", *SIAM Journal on Computing* 17(2):373–386, 1988
