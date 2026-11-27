# Unbounded pure price of anarchy on unrelated machines

For every $K \ge 1$ there is a load-balancing game with two jobs on two unrelated machines with $\mathrm{OPT} = 1$ and a pure Nash equilibrium of makespan $K$.

## Proof sketch

Let job $1$ take time $1$ on machine $1$ and $K$ on machine $2$, and job $2$ symmetric; assigning each job to its slow machine is an equilibrium because moving would cost $1 + K > K$.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)

## Sources

- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
