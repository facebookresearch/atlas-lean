# Moment duality, one generation (polynomial identity)

For all natural numbers $M \ne 0$ and $n$ and every real $x$,

$$\sum_{i=0}^{M} \binom{M}{i} x^i (1 - x)^{M - i} \Bigl(\frac{i}{M}\Bigr)^{n} = \sum_{k=0}^{n} p_M(n, k)\, x^k,$$

where $p_M(n, k) = S(n, k)\, M(M-1)\cdots(M-k+1)/M^n$ is the [Wright–Fisher transition probability of the lineage count](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/wf-lineage-prob.md). For $x \in [0, 1]$, the $n$-th moment of the allele frequency after one generation equals the generating function of the number of distinct parents of $n$ sampled genes.

## Sources

- S. N. Ethier and R. C. Griffiths, *The transition function of a Fleming–Viot process*, Ann. Probab. 21 (1993), 1571–1590.
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), ch. 7.
