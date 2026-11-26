# Indexed signature scheme

A *$q$-indexed signature scheme* signs pairs $(u, m)$ with an index $u \in \{1, \dots, q\}$. It is *indexed EUF-CMA secure* if every efficient adversary whose signing queries use pairwise distinct indices outputs a valid signature on a new pair $(u, m)$ only with negligible probability. Many-time Winternitz or Lamport keys stored per index form such a scheme with $q$ one-time keys.

## Depends on

- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)
- [Signature forgery experiment](../../../security-games/generic-security-games/sig-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
