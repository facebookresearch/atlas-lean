# Prefix-free pseudorandom function

Let $F : K \times X^{\le \ell} \to Y$ be a keyed function on sequences of at most $\ell$ blocks. An adversary is *prefix-free* if no query it makes is a proper prefix of another of its queries. $F$ is a *prefix-free PRF* if every efficient prefix-free adversary has negligible advantage in distinguishing $F(k, \cdot)$ for uniform $k$ from a uniformly random function $X^{\le\ell} \to Y$. An *extendable* prefix-free PRF additionally remains secure when one fresh block is appended to every query.

## Depends on

- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)
- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare, J. Kilian and P. Rogaway, "The Security of the Cipher Block Chaining Message Authentication Code", Journal of Computer and System Sciences 61(3), 2000.
