# Gene frequency spectrum of the infinitely many genes model

**Model.** Genomes of a haploid (e.g. bacterial) population evolve along a Kingman coalescent genealogy of a sample of size $n$. Besides a fixed set of essential core genes, each lineage gains new genes, never seen before, at rate $\theta_1/2$ (infinitely many genes assumption) and loses each gene it carries at rate $\rho/2$, independently. Let $G_k$ be the number of genes present in exactly $k$ of the $n$ sampled genomes (the gene frequency spectrum, excluding the core).

**Theorem.** For $k = 1, \dots, n$,

$$\mathbb E[G_k] = \frac{\theta_1}{k}\,\frac{(n-k+1)(n-k+2)\cdots n}{(n-k+\rho)(n-k+1+\rho)\cdots(n-1+\rho)}.$$

For $k < n$ the ratio is a product of $k$ factors $\frac{n-k+i}{n-k+i-1+\rho}$, $i = 1,\dots,k$, so large loss rates $\rho$ concentrate the spectrum on rare genes, while as $\rho \to 0$ the class $k = n$ grows like $\theta_1/\rho$ (genes that are never lost accumulate in every genome). Summing over $k$ gives the expected size of the dispensable pangenome in the sample.

## Expansion

A gene gained at a point of the genealogy is inherited by the descendants below that point unless lost on the way, so its sample frequency is the number of leaves reached by a branching subtree with killing at rate $\rho/2$ per lineage. Going backward in time, with $j$ lineages present, coalescences happen at rate $\binom j2$ and the $j$ lineages carrying a gene are lost at total rate $j\rho/2$; the family sizes evolve like a Hoppe-type urn in which gene loss plays the role of the immigration weight. Summing over gain events along the tree, with the Poisson gain intensity $\theta_1/2$ per unit branch length, produces the product formula.

## Sources

- Franz Baumdicker, "The site frequency spectrum of dispensable genes", *Theoretical Population Biology* 100 (2015), 13–25, <https://doi.org/10.1016/j.tpb.2014.12.001>; preprint arXiv:1407.2488, <https://doi.org/10.48550/arXiv.1407.2488>. Numbering of the arXiv version: Section 2 (model), Theorem 2, Theorem 5 (Hoppe's urn for family sizes).
