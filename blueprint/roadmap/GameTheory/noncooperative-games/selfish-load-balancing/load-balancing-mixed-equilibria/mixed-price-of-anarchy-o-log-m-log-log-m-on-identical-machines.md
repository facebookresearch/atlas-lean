# Mixed price of anarchy O(log m / log log m) on identical machines

For $m \ge 3$ identical machines, every mixed Nash equilibrium has expected load less than $2\, \mathrm{OPT}$ on every machine and expected makespan $O(\log m / \log\log m) \cdot \mathrm{OPT}$.

## Proof sketch

The equilibrium condition bounds every expected load by $2\,\mathrm{OPT}$; the weighted Chernoff bound with $1 + \delta \approx \log m / \log\log m$ and a union bound over machines bound the expected maximum.

## Depends on

- [Expected makespan of a mixed profile in load balancing](expected-makespan-of-a-mixed-profile-in-load-balancing.md)

## Proof depends on

- [Weighted Chernoff tail for machine loads](weighted-chernoff-tail-for-machine-loads.md)
- [Mixed Nash equilibria of load balancing and uniqueness of totally mixed equilibria](mixed-nash-equilibria-of-load-balancing-and-uniqueness-of-totally-mixed-equilibr.md)

## Sources

- Elias Koutsoupias and Christos H. Papadimitriou, "Worst-Case Equilibria", STACS 99: 16th Annual Symposium on Theoretical Aspects of Computer Science, 1999.
- Artur Czumaj and Berthold Vocking, "Tight Bounds for Worst-Case Equilibria", Proceedings of the Thirteenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2002.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007, Theorem 20.13 (every Nash equilibrium on $m$ identical machines has cost $O(\log m/\log\log m) \cdot \mathrm{opt}$) and its proof (the maximum expected load is less than $2\,\mathrm{opt}$).
