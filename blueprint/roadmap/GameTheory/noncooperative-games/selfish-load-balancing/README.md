# Selfish load balancing

Selfish agents each place one task on one of $m$ identical machines and want the least loaded machine; the social cost is the makespan, the largest load. This is the model in which Koutsoupias and Papadimitriou (STACS 1999) introduced the *coordination ratio*, now called the price of anarchy: the worst ratio between the social cost of a Nash equilibrium and the optimum. For pure equilibria on identical machines the price of anarchy is exactly $2 - 2/(m+1)$ (Vöcking, *Algorithmic Game Theory*, Chapter 20, Theorem 20.5 and Exercise 20.2); for mixed equilibria, which Koutsoupias and Papadimitriou studied, it grows like $\log m / \log \log m$ (Theorems 20.12 and 20.13, from Koutsoupias and Papadimitriou's lower bound and the analyses of Czumaj and Vöcking and of Koutsoupias, Mavronicolas and Spirakis).

- [Load of a machine](load.md)
- [Makespan](makespan.md)
- [Pure Nash equilibrium of the load balancing game](is-pure-nash.md)
- [Loads are nonnegative](load-nonneg.md)
- [Every load is at most the makespan](load-le-makespan.md)
- [Loads add up to the total weight](sum-load.md)
- [Average load bound](sum-weight-le-mul-makespan.md)
- [A single task bounds every makespan](weight-le-makespan.md)
- [Price of anarchy for pure equilibria on identical machines (multiplicative form)](succ-mul-makespan-le.md)
- [Price of anarchy for pure equilibria on identical machines](makespan-le-of-is-pure-nash.md)

## Related topics

- [Selfish routing and the price of anarchy](../selfish-routing-and-the-price-of-anarchy/README.md): the nonatomic counterpart, with price of anarchy $4/3$ for affine latencies.
- [Atomic congestion games with affine delays](../atomic-congestion-games-with-affine-delays/README.md): atomic players and a utilitarian social cost, price of anarchy $5/2$.
- [List scheduling on identical machines](../../../ComputerScience/approximation-algorithms/list-scheduling-on-identical-machines/README.md): Graham's greedy algorithm for the same makespan problem; its $2 - 1/m$ analysis is the model for the equilibrium bound (Vöcking, Section 20.2.1).
- [Nash's theorem](../nash-s-theorem/README.md): existence of mixed equilibria; load balancing games even have pure ones (Vöcking, Proposition 20.3).
