# CBC-MAC is a prefix-free PRF

If $F$ is a PRF on $n$-bit blocks with $2^{-n}$ negligible, then raw CBC-MAC on messages of $1$ to $\ell(n)$ blocks is a prefix-free PRF. For a prefix-free adversary making $Q$ queries,

$$\mathrm{PRFadv}^{\mathrm{pf}}(\mathrm{CBC}) \le \mathrm{PRFadv}(F) + \frac{Q^2 \ell^2}{2^n}.$$

In particular, on messages of a fixed number of blocks CBC-MAC is a PRF and a strongly unforgeable MAC.

## Proof sketch

Replace $F$ by a random function. In the evaluation tree of the queries, an internal chaining value feeds a fresh input unless two distinct prefixes produce the same chaining-value-plus-block input; this collision has probability at most $Q^2\ell^2/2^n$ by a birthday argument, and absent it every final output (not a prefix of another query) is a fresh uniform value.

## Depends on

- [CBC-MAC](cbc-mac.md)
- [Prefix-free pseudorandom function](../pseudorandom-function-constructions/prefix-free-pseudorandom-function.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)
- [The PRP/PRF switching lemma](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/switching-lemma.md)

## Sources

- M. Bellare, J. Kilian and P. Rogaway, "The Security of the Cipher Block Chaining Message Authentication Code", Journal of Computer and System Sciences 61(3), 2000.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
