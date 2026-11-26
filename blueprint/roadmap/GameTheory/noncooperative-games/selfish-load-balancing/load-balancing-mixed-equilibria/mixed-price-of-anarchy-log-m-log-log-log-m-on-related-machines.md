# Mixed price of anarchy Θ(log m / log log log m) on related machines

For load-balancing games on $m \ge 16$ uniformly related machines, every mixed Nash equilibrium has expected makespan $O(\log m / \log\log\log m) \cdot \mathrm{OPT}$. Conversely, for infinitely many $m$ there are instances on $m$ related machines (replicating the speed tiers of the pure lower-bound construction) with a mixed Nash equilibrium of expected makespan $\Omega(\log m / \log\log\log m) \cdot \mathrm{OPT}$.

## Proof sketch

Expected loads obey the same factorial speed-prefix bound as pure loads, giving $O(\log m/\log\log m)$ expected load; random fluctuations above the expected load on fast machines add only an additive $O(\log m / \log\log\log m) \cdot \mathrm{OPT}$ term by Chernoff bounds over speed-doubling groups. The lower bound places each replicated tier's jobs uniformly over the tier above.

## Depends on

- [Expected makespan of a mixed profile in load balancing](expected-makespan-of-a-mixed-profile-in-load-balancing.md)

## Proof depends on

- [Pure price of anarchy O(log m / log log m) on related machines](../load-balancing-pure-equilibria/pure-price-of-anarchy-o-log-m-log-log-m-on-related-machines.md)
- [Pure price of anarchy Ω(log m / log log m) on related machines](../load-balancing-pure-equilibria/pure-price-of-anarchy-log-m-log-log-m-on-related-machines.md)
- [Weighted Chernoff tail for machine loads](weighted-chernoff-tail-for-machine-loads.md)

## Sources

- Artur Czumaj and Berthold Vocking, "Tight Bounds for Worst-Case Equilibria", Proceedings of the Thirteenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2002.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
