# CBC mode with a random IV is CPA secure

If $E$ is a PRP with super-polynomial block space ($2^{-b(n)}$ negligible), then randomized CBC is CPA secure (many-query left-or-right security) on whole-block messages. For an adversary encrypting at most $Q\ell$ blocks in total,

$$\mathrm{CPAadv} \le 2\,\mathrm{PRPadv}(E) + \frac{2 (Q\ell)^2}{2^{b}}.$$

## Proof sketch

Replace $E$ by a random function (switching lemma). Then every input to the function is $c_{j-1} \oplus m_j$ with $c_{j-1}$ uniform and fresh unless a collision among the $Q\ell$ inputs occurs; absent collisions every ciphertext block is a fresh uniform value independent of the message.

## Depends on

- [CBC mode with a random initial value](cbc-mode.md)
- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)

## Proof depends on

- [Switching lemma with the birthday bound](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/switching-lemma-le.md)
- [Fundamental lemma of game playing for stateful oracle handlers](../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare, A. Desai, E. Jokipii and P. Rogaway, "A Concrete Security Treatment of Symmetric Encryption", Proceedings of the 38th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1997.
