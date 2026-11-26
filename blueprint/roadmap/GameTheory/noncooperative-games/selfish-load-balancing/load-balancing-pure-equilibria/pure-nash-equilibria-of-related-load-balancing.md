# Pure Nash equilibria of related load balancing

An assignment $A$ in a load-balancing game on uniformly related machines is a pure Nash equilibrium if and only if for every job $i$ and every machine $k \ne A(i)$, $\ell_{A(i)}(A) \le \ell_k(A) + w_i / s_k$. Moreover $\sum_i w_i \le \bigl(\sum_j s_j\bigr)\, \mathrm{OPT}$.

## Proof sketch

Moving job $i$ to $k$ gives it cost $\ell_k + w_i/s_k$. The volume bound follows since each machine processes at most $s_j \cdot \mathrm{OPT}$ weight in an optimal schedule.

## Depends on

- [Load balancing on uniformly related and unrelated machines](load-balancing-on-uniformly-related-and-unrelated-machines.md)

## Sources

- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
