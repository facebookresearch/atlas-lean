# Pure price of anarchy O(log m / log log m) on related machines

Let $A$ be a pure Nash equilibrium of a load-balancing game on $m$ uniformly related machines in which some job has positive weight, so that $\mathrm{OPT} > 0$. If $\max_j \ell_j(A) \ge (c + 1)\,\mathrm{OPT}$ for an integer $c$, then $c! \le m$ (Vocking, proof of Theorem 20.7). Consequently

$$
\max_j \ell_j(A) = O\Bigl(\frac{\log m}{\log\log m}\Bigr)\mathrm{OPT}
$$

(Vocking, Theorem 20.7).

## Proof sketch

Order machines by speed and let $L_k$ be the fastest prefix of machines with load at least $k\,\mathrm{OPT}$. Equilibrium plus the volume argument give $(k+1)|L_{k+1}| \le |L_k|$, so the prefix sizes shrink factorially, and since $\Gamma^{-1}(m) = \Theta(\log m / \log\log m)$, the inequality $c! \le m$ gives the stated bound.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)

## Proof depends on

- [Pure Nash equilibria of related load balancing](pure-nash-equilibria-of-related-load-balancing.md)

## Sources

- Artur Czumaj and Berthold Vocking, "Tight Bounds for Worst-Case Equilibria", Proceedings of the Thirteenth Annual ACM-SIAM Symposium on Discrete Algorithms, 2002.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007, Theorem 20.7.
