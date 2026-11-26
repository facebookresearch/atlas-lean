# Verification queries do not weaken strong MAC security

A MAC is strongly unforgeable with verification queries if and only if it is strongly unforgeable in the standard game. For an adversary making $Q_v$ verification queries, the winning probability with verification queries is at most $Q_v$ times the standard strong forgery probability of a reduction.

## Proof sketch

The reduction guesses which verification query is the first valid fresh pair, answers all earlier verification queries with "reject" except replays of signed pairs, and outputs the guessed query as its forgery.

## Depends on

- [MAC security with verification queries](mac-security-with-verification-queries.md)
- [Strong MAC forgery experiment](../../security-games/generic-security-games/mac-strong-game.md)

## Proof depends on

- [Planted-query guessing: bounding a bad event by a reduction that guesses its index](../../security-games/identical-until-bad-oracle-handlers/planted-query-guessing-bound.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
