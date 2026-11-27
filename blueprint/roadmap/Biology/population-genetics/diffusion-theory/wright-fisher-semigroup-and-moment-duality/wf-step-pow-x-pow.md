# Moment duality over several Wright–Fisher generations

For natural numbers $M \ne 0$, $m$ and $N$ and every $n \in \{0, \dots, N\}$, the $m$-th power of the [Wright–Fisher generation operator](wf-step.md) maps $x \mapsto x^n$ on $[0, 1]$ to

$$x \mapsto \sum_{k=0}^{N} P_{N,M}^{\,m}(n, k)\, x^k,$$

where $P_{N,M}$ is the [Wright–Fisher transition matrix of the lineage count](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/wf-lineage-matrix.md): the $n$-th moment of the allele frequency after $m$ generations is the generating function of the number of ancestors, $m$ generations back, of $n$ sampled genes.
