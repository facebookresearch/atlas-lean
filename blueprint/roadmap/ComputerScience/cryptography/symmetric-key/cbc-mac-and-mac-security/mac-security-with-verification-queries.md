# MAC security with verification queries

In the *strong unforgeability game with verification queries*, the adversary interleaves signing queries $m$ (answered with $t \leftarrow S(k, m)$) and verification queries $(m, t)$ (answered with $V(k, m, t)$). It wins if some verification query that accepts is a pair $(m, t)$ not previously returned by the signing oracle. The MAC is SUF-CMA secure with verification queries if every efficient adversary wins with negligible probability.

## Depends on

- [Strong MAC forgery experiment](../../security-games/generic-security-games/mac-strong-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
