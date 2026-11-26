# Pure price of anarchy O(log m / log log m) on related machines

Let $A$ be a pure Nash equilibrium of a load-balancing game on $m$ uniformly related machines. If $\max_j \ell_j(A) \ge (c + 1)\,\mathrm{OPT}$ for an integer $c$, then $c! \le m$. Consequently, for $m \ge 3$,

$$
\max_j \ell_j(A) \le \Bigl(\frac{4 \log m}{\log\log m} + 3\Bigr)\mathrm{OPT}.
$$

## Proof sketch

Order machines by speed and let $L_k$ be the fastest prefix of machines with load at least $k\,\mathrm{OPT}$. Equilibrium plus the volume argument give $(k+1)|L_{k+1}| \le |L_k|$, so the prefix sizes shrink factorially, and Stirling's estimate turns $c! \le m$ into the stated bound.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)

## Proof depends on

- [Pure Nash equilibria of related load balancing](pure-nash-equilibria-of-related-load-balancing.md)

## Sources

- Artur Czumaj and Berthold Vocking, "Tight Bounds for Worst-Case Equilibria", Proceedings of the Thirteenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2002.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
