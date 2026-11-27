# The 2m/(m+1) pure price of anarchy on identical machines is exact

For every $m \ge 1$ there is an instance with $2m$ jobs on $m$ identical machines and a pure Nash equilibrium whose makespan equals $\frac{2m}{m+1}\mathrm{OPT}$, so the upper bound $\frac{2m}{m+1}$ is attained for every $m$. Moreover, every pure Nash equilibrium of $3$ jobs on $2$ identical machines is optimal, and if every job weighs at most $B$ then every pure Nash equilibrium on $m$ identical machines has makespan at most $\mathrm{OPT} + (1 - 1/m) B$.

## Proof sketch

The tight instance pairs $2m$ jobs so that in the equilibrium one machine holds two medium jobs while the optimum spreads all jobs evenly; the additive bound follows because the last job on a most loaded machine could move to a least loaded machine.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)
- [Price of anarchy for pure equilibria on identical machines](../makespan-le-of-is-pure-nash.md)

## Proof depends on

- [Pure Nash equilibria of related load balancing](pure-nash-equilibria-of-related-load-balancing.md)

## Sources

- G. Finn and Ellis Horowitz, "A Linear Time Approximation Algorithm for Multiprocessor Scheduling", BIT Numerical Mathematics, 1979.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
