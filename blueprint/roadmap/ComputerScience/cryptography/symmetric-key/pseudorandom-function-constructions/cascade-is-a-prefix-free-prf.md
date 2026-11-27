# The cascade construction is a prefix-free pseudorandom function

Let $F : K \times X \to K$ be a PRF. The *cascade* $F^*(k, (x_1, \dots, x_\ell)) = k_\ell$ with $k_0 = k$ and $k_i = F(k_{i-1}, x_i)$ is a prefix-free PRF on sequences of at most $L$ blocks. For every prefix-free adversary making $Q$ queries, $\mathrm{PRFadv}(F^*) \le Q L \cdot \mathrm{PRFadv}(F)$ for a PRF adversary that is an elementary wrapper around the given adversary: besides running it, the wrapper evaluates $F$ on at most $QL$ inputs, samples the replaced keys and keeps lookup tables for them (Boneh–Shoup, Theorem 6.4).

## Proof sketch

Hybrid over tree depth: in hybrid $j$ the keys at depth $j$ of the evaluation tree are replaced by independent random keys for distinct prefixes. Each step replaces one level of evaluations by random functions using a multi-key reduction with at most $Q$ keys, and prefix-freeness guarantees the final outputs are fresh random keys.

## Depends on

- [Prefix-free pseudorandom function](prefix-free-pseudorandom-function.md)
- [Elementary wrappers](../../security-games/asymptotic-security/elementary-wrappers.md)

## Proof depends on

- [Several independent keys of a pseudorandom function](multi-key-prf-hybrid.md)
- [Hybrid argument](../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare, J. Kilian and P. Rogaway, "The Security of the Cipher Block Chaining Message Authentication Code", Journal of Computer and System Sciences 61(3), 2000.
