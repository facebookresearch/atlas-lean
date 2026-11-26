# Prepending the key to a random oracle gives a PRF

In the random oracle model with oracle $O : M \to T$, let $F(k, x) = O(\langle k, x\rangle)$ for an injective encoding of key–input pairs. For every adversary making at most $Q_{\mathrm{ro}}$ random-oracle queries (and any number of $F$-queries, with unbounded computation),

$$\mathrm{PRFadv}^{\mathrm{ro}}(F) \le \frac{Q_{\mathrm{ro}}}{|K|}.$$

Hence $F$ is a secure PRF when $1/|K|$ is negligible.

## Proof sketch

The real and ideal experiments are identical until the adversary queries the oracle at a point whose key component equals the secret key; each oracle query hits it with probability at most $1/|K|$ since the key is independent of the adversary's view before that event.

## Depends on

- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)
- [Accumulated bad-event probability over a query-bounded run](../../security-games/identical-until-bad-oracle-handlers/accumulated-bad-event-probability.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and P. Rogaway, "Random Oracles are Practical: A Paradigm for Designing Efficient Protocols", Proceedings of the 1st ACM Conference on Computer and Communications Security (CCS), 1993.
