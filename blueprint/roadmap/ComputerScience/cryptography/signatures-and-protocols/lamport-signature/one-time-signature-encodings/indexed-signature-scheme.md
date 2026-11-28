# Indexed signature scheme

A *$q$-indexed signature scheme* is a signature scheme whose messages are pairs $(u, m)$ with an index $u \in \{1, \dots, q\}$ and whose signing algorithm is deterministic. It is *indexed EUF-CMA secure* if every efficient adversary making at most $q$ signing queries, whose signing queries use pairwise distinct indices, outputs a valid signature on a new pair $(u, m)$ only with negligible probability. One-time Winternitz or Lamport keys, one per index, form such a scheme with $q$ one-time keys (with signing derandomized, for instance by a PRF, where the one-time scheme signs randomly).

## Depends on

- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)
- [Signature forgery experiment](../../../security-games/generic-security-games/sig-game.md)
- [Efficient adversaries](../../../security-games/asymptotic-security/efficient-adversaries.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)
## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
