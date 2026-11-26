# Cache-complexity lower bound for sorting

In the [ideal-cache model](the-ideal-cache-model.md) with a cache of $Z$ words and lines of $L$ words satisfying the tall-cache assumption $Z = \Omega(L^2)$, every comparison-based sorting algorithm incurs $\Omega\bigl(1 + (n/L)(1 + \log_Z n)\bigr)$ cache misses to sort $n$ elements. So [funnelsort](funnelsort.md) and cache-oblivious distribution sort are cache-optimal.

## Depends on

- [The ideal-cache model](the-ideal-cache-model.md)

## Proof depends on

- [The external-memory model](../external-memory-algorithms/the-external-memory-model.md): the lower bound $\Omega((n/L)\log_{Z/L}(n/Z))$ of Aggarwal and Vitter on sorting carries over to the ideal-cache model, and the tall-cache assumption with the trivial bounds $\Omega(1)$ and $\Omega(n/L)$ gives the form above.

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th Annual Symposium on Foundations of Computer Science*, 1999, Section 4, Theorem 8 and its proof.
