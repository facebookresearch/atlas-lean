# Counter-mode encryption as an oracle computation

Let $Y$ be an additive commutative group. For a message $m \in Y^\ell$ and a counter $\mathrm{ctr} \in \mathbb{Z}/N$, the oracle computation [queries](query-vec.md) the keyed function at $\mathrm{ctr} + i$ in order for $i = 0, \dots, \ell - 1$, obtaining $ks \in Y^\ell$, and returns $(\mathrm{ctr}, ks + m)$. It does not itself sample the counter.
