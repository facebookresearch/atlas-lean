# Mixed price of anarchy Θ(log m / log log log m) on related machines

For load-balancing games on $m$ uniformly related machines, every mixed Nash equilibrium has expected makespan $O(\log m / \log\log\log m) \cdot \mathrm{OPT}$ (Vocking, Theorem 20.15). Conversely, for every $m$ there is an instance on $m$ related machines, obtained from the pure lower-bound construction, with a mixed Nash equilibrium of expected makespan $\Omega(\log m / \log\log\log m) \cdot \mathrm{OPT}$ (Vocking, Theorem 20.18).

## Proof sketch

Expected loads obey the same factorial speed-prefix bound as pure loads, giving $O(\log m/\log\log m)$ expected load; random fluctuations above the expected load on fast machines add only an additive $O(\log m / \log\log\log m) \cdot \mathrm{OPT}$ term by Chernoff bounds over speed-doubling groups. The lower bound lets the tasks of one middle machine group of the pure construction choose a machine of that group uniformly at random; a balls-into-bins estimate gives the extra $\log\log m / \log\log\log m$ factor.

## Depends on

- [Expected makespan of a mixed profile in load balancing](expected-makespan-of-a-mixed-profile-in-load-balancing.md)

## Proof depends on

- [Pure price of anarchy O(log m / log log m) on related machines](../load-balancing-pure-equilibria/pure-price-of-anarchy-o-log-m-log-log-m-on-related-machines.md)
- [Pure price of anarchy Ω(log m / log log m) on related machines](../load-balancing-pure-equilibria/pure-price-of-anarchy-log-m-log-log-m-on-related-machines.md)
- [Weighted Chernoff tail for machine loads](weighted-chernoff-tail-for-machine-loads.md)

## Sources

- Artur Czumaj and Berthold Vocking, "Tight Bounds for Worst-Case Equilibria", Proceedings of the Thirteenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2002.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007, Theorems 20.15 and 20.18.
