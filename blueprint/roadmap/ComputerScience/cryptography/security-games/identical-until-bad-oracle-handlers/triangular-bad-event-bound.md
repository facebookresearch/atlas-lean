# Triangular (birthday-type) bound for linearly growing bad sets

Let a stateful handler carry a natural-number size $\mathrm{size}(\sigma)$ on states. Suppose that from a good state $\sigma$ every query triggers a bad state with probability at most $\mathrm{size}(\sigma)\cdot\delta$ and increases the size by at most $1$. Then every oracle program making at most $q$ queries, started in a good state $\sigma_0$, reaches a bad state with probability at most

$$\delta\left(q \cdot \mathrm{size}(\sigma_0) + \binom{q}{2}\right).$$

With $\mathrm{size}(\sigma_0) = 0$ and $\delta = 1/N$ this is the birthday bound $\binom{q}{2}/N$ for collisions among $q$ lazily sampled answers in a set of size $N$.

## Proof sketch

Apply the accumulation bound with the state-dependent bound $\delta \cdot \mathrm{size}$; along any path the size before the $i$-th query is at most $\mathrm{size}(\sigma_0) + i - 1$, and summing over $i = 1, \dots, q$ gives the triangular sum.

## Depends on

- [Stateful oracle handlers that are identical until bad](identical-until-bad-handlers.md)

## Proof depends on

- [Accumulated bad-event probability over a query-bounded run](accumulated-bad-event-probability.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and P. Rogaway, "The Security of Triple Encryption and a Framework for Code-Based Game-Playing Proofs", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, 2006.
