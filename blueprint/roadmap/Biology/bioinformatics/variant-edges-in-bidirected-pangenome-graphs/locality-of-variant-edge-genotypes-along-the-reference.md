# Locality of variant-edge genotypes along the reference

Let $B$ be a bidirected pangenome graph that contains the linear reference genome $L$ as a path without repeated binodes, and choose a depth-first-search reference tree $T$ whose first branch is $L$ (see [Bidirected pangenome graphs and variant edges](bidirected-pangenome-graphs-and-variant-edges.md)). Positions are assigned as follows: a binode on $L$ gets its reference coordinate; any other binode $\{u, u^c\}$ gets the largest position of a node of $L$ that reaches $u$ in $T$. A variant edge $e = (u, v)$ gets the interval $\mathrm{pos}(e) = [\mathrm{pos}(u), \mathrm{pos}(v)]$.

**Theorem.** If $B$ has no inversion edges and $\mathrm{pos}(e) = [a, b]$, then for every walk $W$ the count $x_e(W)$ is determined by the counts $x_\eta(W)$ of the variant edges $\eta$ with $\mathrm{pos}(\eta) \cap [a, b] \ne \varnothing$.

Thus each variant has a well-defined interval on the linear reference, and its genotype is a function of the genotypes of overlapping variants only, which is what makes cataloguing pangenome variants by reference position consistent.

## Depends on

- [Bidirected pangenome graphs and variant edges](bidirected-pangenome-graphs-and-variant-edges.md)

## Proof depends on

- [Variant-edge genotypes determine walks](variant-edge-genotypes-determine-walks.md)

## Proof sketch

Positions are monotone along $T$: if $T$ has a path from $u$ to $v$ then $\mathrm{pos}(u) \le \mathrm{pos}(v)$, and a tree path between nodes of different positions passes through the ancestor on $L$ that carries the later position. The proof combines this monotonicity with the visit-count lemma: for a binode $b$ positioned outside $[\mathrm{pos}(u), \mathrm{pos}(v)]$ the quantity $|D(b)\cap\mathrm{sinks}(W)| - |D(b)\cap\mathrm{sources}(W)|$ is invariant, and from this the traversal count of $e$ is expressed through the variant edges whose intervals overlap $[a, b]$ (Theorem 6 of the source). The reference tree itself is built by a depth-first search that prefers, at each branch, either the outgoing edge used by most haplotypes or the continuation of a prioritized haplotype; the theorem holds for any such choice.

## Sources

- P. Salehi Nowbandegani, S. Zhang, H. Hu, H. Li, L. J. O'Connor, "Defining and cataloging variants in pangenome graphs", Cell Genomics (2026), <https://doi.org/10.1016/j.xgen.2026.101327> (PMC13576716).
