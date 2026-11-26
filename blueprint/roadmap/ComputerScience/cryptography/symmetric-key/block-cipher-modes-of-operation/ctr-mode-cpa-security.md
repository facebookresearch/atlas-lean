# Randomized counter mode is CPA secure

If $F$ is a PRF with $b$-bit inputs, $2^{-b}$ negligible, then randomized counter mode is CPA secure. For $Q$ encryption queries of at most $\ell$ blocks, $\mathrm{CPAadv} \le 2\,\mathrm{PRFadv}(F) + \frac{4Q^2\ell}{2^b}$.

## Proof sketch

With a random function the pads are uniform unless two counter intervals of length $\ell$ starting at uniform points overlap, which happens for a given pair with probability at most $2\ell/2^b$.

## Depends on

- [Randomized counter (CTR) mode](randomized-counter-mode.md)
- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare, A. Desai, E. Jokipii and P. Rogaway, "A Concrete Security Treatment of Symmetric Encryption", Proceedings of the 38th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1997.
