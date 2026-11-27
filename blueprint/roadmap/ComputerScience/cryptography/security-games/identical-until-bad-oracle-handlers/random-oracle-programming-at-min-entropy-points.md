# Random-oracle programming at high-min-entropy points

Consider an oracle handler (such as a signing or zero-knowledge simulator) that makes at most $T$ *programming writes* in a run, writes at rejected trials included: for each, it samples fresh coins $\tau$, independent of everything before, and a value $v$ uniform in the oracle's range and independent of everything else, and writes $v$ at the point $\pi(\tau)$, overwriting any value already defined there, where every such point has guessing probability at most $\delta$ (that is, $\Pr_\tau[\pi(\tau) = x] \le \delta$ for every $x$). Let at most $H$ oracle points be queried other than by programming writes (directly by the adversary or by the handler on its behalf). Compare this *programmed* experiment with the *unprogrammed* one in which the handler, instead of writing, takes as $v$ the oracle's value at $\pi(\tau)$ (keeping a value already defined there, and otherwise defining a fresh uniform one), everything else unchanged. The two experiments are identical until a programmed point is already defined when it is programmed, so the adversary's views, and hence its outputs, differ in statistical distance by at most the probability of that event, which is at most $T \cdot H \cdot \delta + \binom{T}{2}\delta \le T(H + T)\delta$, the second term covering collisions among programmed points. The comparison is with the unprogrammed oracle the handler reads, not with an experiment in which the writes are erased: when the handler's answers reveal a programmed point and its value, as signatures do, erasing the writes can change the adversary's output distribution by almost $1$.

## Proof sketch

When the $i$-th point is programmed, at most $H + i - 1$ points are defined, and this set is fixed before the fresh coins $\tau$ are drawn, so the point is already defined with probability at most $(H + i - 1)\delta$. If it is not, the programmed value and the value the unprogrammed handler reads are both fresh uniform values, so the experiments agree until that bad event; summing over $i \le T$ and applying the fundamental lemma gives the bound.

## Depends on

- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Guessing probability, min-entropy and collision probability](../../randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Proof depends on

- [Effect of overwriting one entry of a memoized random oracle](overwritten-random-oracle-entry.md)
- [Accumulated bad-event probability over a query-bounded run](accumulated-bad-event-probability.md)
- [Fundamental lemma of game playing for stateful oracle handlers](fundamental-lemma-for-stateful-handlers.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and P. Rogaway, "Random Oracles are Practical: A Paradigm for Designing Efficient Protocols", Proceedings of the 1st ACM Conference on Computer and Communications Security (CCS), 1993.
