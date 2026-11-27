# Finite improvement property and price of stability 1 for load balancing

Every load-balancing game on uniformly related machines (zero-weight jobs allowed), and every load-balancing game on unrelated machines with strictly positive processing times, has the finite improvement property. No improving move increases the makespan, so improvement dynamics started from an optimal assignment end at a pure Nash equilibrium of makespan $\mathrm{OPT}$: the price of stability is $1$.

## Proof sketch

An improving move of a job with positive weight (or positive processing times) strictly decreases the sorted load vector lexicographically: the job leaves a machine whose load is strictly greater than the new load of the target. A zero-weight job changes no load and moves to a machine of strictly smaller load, so only finitely many such moves occur between two moves of positive-weight jobs. Termination follows from finiteness, and the moving job's new machine stays below the old maximum.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)
- [Finite improvement property](../../potential-games/well-founded-improving-move.md)
- [Price of anarchy and price of stability](../../no-regret-dynamics/remaining-clauses-of-social-cost-price-of-anarchy-and-stabil.md)

## Proof depends on

- [Pure Nash equilibria of related load balancing](pure-nash-equilibria-of-related-load-balancing.md)

## Sources

- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
