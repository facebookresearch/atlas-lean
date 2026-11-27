# Multi-challenge left-or-right CPA security from single-challenge security

Let a symmetric cipher be secure in the CPA experiment with one left-or-right challenge and an ordinary encryption oracle. Then it is secure in the experiment with $Q$ adaptive left-or-right challenges under a common bit, with advantage at most $Q$ times the single-challenge advantage of a reduction that answers the other challenges with its encryption oracle.

## Proof sketch

Hybrid $H_i$ answers the first $i$ challenges with the right message and the rest with the left; the reduction plants its challenge at a random index and uses its encryption oracle for the others.

## Depends on

- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)

## Proof depends on

- [Hybrid argument](../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- M. Bellare, A. Desai, E. Jokipii and P. Rogaway, "A Concrete Security Treatment of Symmetric Encryption", Proceedings of the 38th Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1997.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
