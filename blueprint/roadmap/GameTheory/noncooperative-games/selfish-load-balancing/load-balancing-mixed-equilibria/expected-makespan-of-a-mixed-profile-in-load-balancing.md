# Expected makespan of a mixed profile in load balancing

In a load-balancing game on related machines, a mixed profile assigns to each job $i$ a distribution $p_i$ over machines, jobs choosing independently. The *expected load* of machine $j$ is $\mathbb{E}[\ell_j] = \sum_i p_i(j) w_i / s_j$, and the social cost is the *expected makespan* $\mathbb{E}_{A \sim p}[\max_j \ell_j(A)]$.

## Depends on

- [Load balancing on uniformly related and unrelated machines](../load-balancing-pure-equilibria/load-balancing-on-uniformly-related-and-unrelated-machines.md)
- [Mixed Nash equilibrium](../../nash-s-theorem/is-mixed-nash.md)

## Sources

- Elias Koutsoupias and Christos H. Papadimitriou, "Worst-Case Equilibria", STACS 99: 16th Annual Symposium on Theoretical Aspects of Computer Science, 1999.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
