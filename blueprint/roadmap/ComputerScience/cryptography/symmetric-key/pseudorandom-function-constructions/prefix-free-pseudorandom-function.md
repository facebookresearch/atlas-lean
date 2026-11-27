# Prefix-free pseudorandom function

Let $F : K \times X^{\le \ell} \to Y$ be a keyed function on sequences of at most $\ell$ blocks. An adversary is *prefix-free* if no query it makes is a proper prefix of another of its queries. $F$ is a *prefix-free PRF* if every efficient prefix-free adversary has negligible advantage in distinguishing $F(k, \cdot)$ for uniform $k$ from a uniformly random function $X^{\le\ell} \to Y$. $F$ is *extendable* if for every key $k \in K$, all sequences $x, y \in X^{\le \ell - 1}$ (so that their one-block extensions lie in $X^{\le \ell}$) and every common block $a \in X$, $F(k, x) = F(k, y)$ implies $F(k, x \| a) = F(k, y \| a)$. This is a deterministic condition on outputs, not a security game: an *extendable prefix-free PRF* is a prefix-free PRF that is, separately, extendable.

## Depends on

- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)
- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Sources

- M. Bellare, R. Canetti and H. Krawczyk, "Pseudorandom Functions Revisited: The Cascade Construction and its Concrete Security", Proceedings of the 37th Annual Symposium on Foundations of Computer Science (FOCS 1996), IEEE, 1996 (pseudorandomness on prefix-free sets of inputs).
- M. Bellare, J. Kilian and P. Rogaway, "The Security of the Cipher Block Chaining Message Authentication Code", Journal of Computer and System Sciences 61(3), 2000.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, Definition 6.4 (extendability).
