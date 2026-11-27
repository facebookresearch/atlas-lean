# Koutsoupias–Papadimitriou: mixed price of anarchy 3/2 on two identical machines

For every set of jobs with nonnegative weights on two identical machines, every mixed Nash equilibrium has expected makespan at most $\frac32\, \mathrm{OPT}$. Two unit jobs, each choosing a machine uniformly at random, form a mixed Nash equilibrium attaining exactly $\frac32\, \mathrm{OPT}$.

## Proof sketch

Use the equilibrium cost formula to bound each job's expected cost by $(W + w_i)/2$ and the expected makespan by the expected load of the busier machine; combining with $\mathrm{OPT} \ge \max(W/2, \max_i w_i)$ gives $3/2$.

## Depends on

- [Expected makespan of a mixed profile in load balancing](expected-makespan-of-a-mixed-profile-in-load-balancing.md)

## Proof depends on

- [Mixed Nash equilibria of load balancing and uniqueness of totally mixed equilibria](mixed-nash-equilibria-of-load-balancing-and-uniqueness-of-totally-mixed-equilibr.md)

## Sources

- Elias Koutsoupias and Christos H. Papadimitriou, "Worst-Case Equilibria", STACS 99: 16th Annual Symposium on Theoretical Aspects of Computer Science, 1999.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
