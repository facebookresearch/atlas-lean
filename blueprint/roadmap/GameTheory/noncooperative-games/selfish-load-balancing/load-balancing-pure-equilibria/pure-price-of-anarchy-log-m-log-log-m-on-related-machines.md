# Pure price of anarchy Ω(log m / log log m) on related machines

For every integer $k \ge 1$ there is a load-balancing game on uniformly related machines with $k + 1$ speed tiers (tier $t \in \{0, \dots, k\}$ has $k!/t!$ machines of speed $2^t$, so $m = \sum_{t=0}^{k} k!/t! < e \cdot k!$ machines in total) and, for each $t \in \{1, \dots, k\}$, $k!/(t-1)!$ jobs of weight $2^t$, whose optimal makespan is at most $2$ and which has a pure Nash equilibrium of makespan exactly $k$. Hence the pure price of anarchy on $m$ related machines is $\Omega(\log m / \log\log m)$, matching the upper bound.

## Proof sketch

In the optimum each job of weight $2^t$ has its own machine of tier $t - 1$, a load of $2$. In the bad equilibrium each machine of tier $t$ holds $t$ jobs of weight $2^t$, a load of $t$, so the single machine of tier $k$ has load $k$. A job on tier $t$ moving to a machine of tier $j$ would see load $j + 2^{t-j} > t$ if $j < t$, more than $j \ge t + 1$ if $j > t$ and $t + 1$ if $j = t$, so no job gains. The price of anarchy is at least $k/2$, and $m < e \cdot k!$ gives $k = \Omega(\log m / \log\log m)$.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)

## Proof depends on

- [Pure Nash equilibria of related load balancing](pure-nash-equilibria-of-related-load-balancing.md)

## Sources

- Artur Czumaj and Berthold Vocking, "Tight Bounds for Worst-Case Equilibria", Proceedings of the Thirteenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2002.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
