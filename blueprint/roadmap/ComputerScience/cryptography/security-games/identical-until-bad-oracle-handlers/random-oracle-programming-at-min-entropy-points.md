# Random-oracle programming at high-min-entropy points

Consider an oracle handler (such as a signing or zero-knowledge simulator) that, on each of $T$ requests, samples fresh coins $\tau$ and *programs* the random oracle at a point $\pi(\tau)$ determined by those coins, where every such point has guessing probability at most $\delta$ (that is, $\Pr_\tau[\pi(\tau) = x] \le \delta$ for every $x$). Let the adversary make at most $H$ direct oracle queries. Then the visible output distributions of the programmed experiment and of the experiment using an unprogrammed random oracle (with the programming writes erased, including writes at rejected trials) differ in statistical distance by at most $T \cdot H \cdot \delta$, plus $T^2\delta$ for collisions among programmed points.

## Proof sketch

A programmed write is visible only if the adversary queries that point, either before (inconsistency) or after it was written. Each of the $T$ programmed points is hit by each of the $H$ queries with probability at most $\delta$ by the min-entropy assumption, and the union bound over pairs gives the estimate.

## Depends on

- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Guessing probability, min-entropy and collision probability](../../randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Proof depends on

- [Effect of overwriting one entry of a memoized random oracle](overwritten-random-oracle-entry.md)
- [Accumulated bad-event probability over a query-bounded run](accumulated-bad-event-probability.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and P. Rogaway, "Random Oracles are Practical: A Paradigm for Designing Efficient Protocols", Proceedings of the 1st ACM Conference on Computer and Communications Security (CCS), 1993.
