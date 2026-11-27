# Mixed price of anarchy Ω(log m / log log m) on identical machines

With $m$ unit jobs on $m$ identical machines ($\mathrm{OPT} = 1$), the profile in which every job chooses a machine uniformly at random is a totally mixed Nash equilibrium whose expected makespan is $\Omega(\log m / \log\log m)$.

## Proof sketch

By symmetry every machine has the same expected cost, so the uniform profile is an equilibrium; its makespan is the maximum load of $m$ balls in $m$ bins, which exceeds $k$ with probability at least $1/2$ when $k! \approx m$, by a second-moment count of bins with load exactly $k$.

## Depends on

- [Expected makespan of a mixed profile in load balancing](expected-makespan-of-a-mixed-profile-in-load-balancing.md)
- [Maximum load of balls into bins](../../../../ComputerScience/randomized-algorithms/maximum-load-of-balls-into-bins.md)

## Proof depends on

- [Mixed Nash equilibria of load balancing and uniqueness of totally mixed equilibria](mixed-nash-equilibria-of-load-balancing-and-uniqueness-of-totally-mixed-equilibr.md)

## Sources

- Elias Koutsoupias and Christos H. Papadimitriou, "Worst-Case Equilibria", STACS 99: 16th Annual Symposium on Theoretical Aspects of Computer Science, 1999.
- Artur Czumaj and Berthold Vocking, "Tight Bounds for Worst-Case Equilibria", Proceedings of the Thirteenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2002.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
