# Pure price of anarchy Ω(log m / log log m) on related machines

For every $k$ there is a load-balancing game on uniformly related machines with $k + 1$ speed tiers (tier $t$ has $2^{k-t} k!/t!$ machines of speed $2^t$), at most $2^{k+1} k!$ machines in total, optimal makespan at most $1$, and a pure Nash equilibrium of makespan at least about $k$. Hence the pure price of anarchy on $m$ related machines is $\Omega(\log m / \log\log m)$, matching the upper bound.

## Proof sketch

In the bad equilibrium the jobs of weight $2^t$ sit one tier higher than in the optimum, stacking load $k - t$ on tier $t$; the equilibrium inequality is checked tier by tier, and $k \approx \log m / \log\log m$.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)

## Proof depends on

- [Pure Nash equilibria of related load balancing](pure-nash-equilibria-of-related-load-balancing.md)

## Sources

- Artur Czumaj and Berthold Vocking, "Tight Bounds for Worst-Case Equilibria", Proceedings of the Thirteenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2002.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
