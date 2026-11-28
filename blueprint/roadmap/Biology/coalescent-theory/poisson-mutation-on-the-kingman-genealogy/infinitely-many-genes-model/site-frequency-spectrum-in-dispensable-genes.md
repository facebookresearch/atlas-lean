# Site frequency spectrum in dispensable genes and the bias of mutation-rate estimators

In the [infinitely many genes model](gene-frequency-spectrum-of-the-infinitely-many-genes-model.md) with gene gain rate $\theta_1/2$ and gene loss rate $\rho/2$ per lineage, let point mutations occur within gene sequences at rate $\theta_2/2$ (infinitely many sites). For a gene $u$ let $F(u)$ be the number of the $n$ sampled genomes that carry it and $S^u_s$ the number of its mutated sites carried by exactly $s$ of these copies. For an essential core gene the classical result $\mathbb E[C^u_s] = \theta_2/s$ holds.

**Corollary (conditional site frequency spectrum).** For a gene present in exactly $k$ of $n$ genomes and $1 \le s < k$,

$$\mathbb E[S^u_s \mid F(u) = k] = \frac{\theta_2}{s}\,\frac{k}{n}\binom{n-1}{s}^{-1}\sum_{j=0}^{n-s-1}\frac{j+1}{j+1+\rho}\binom{n-j-2}{s-1},$$

and the class of mutations carried by all $k$ copies satisfies

$$\mathbb E[S^u_k \mid F(u) = k] = k\,\theta_2\sum_{j=1}^{n-k+1}\binom{n}{j}^{-1}\frac{1}{j(j-1+\rho)}\binom{n-k}{j-1}, \qquad \mathbb E[S^u_n \mid F(u) = n] = \frac{\theta_2}{\rho}.$$

Moreover $\mathbb E[S^u_s \mid F(u) = k] \le \frac{k}{n}\,\frac{\theta_2}{s}$ for $s < k$.

**Theorem (estimator bias).** For a dispensable gene present in $k$ of $n$ genomes, Watterson's estimator $\widehat\theta_{W,k} = \sum_{s<k} S^u_s / \sum_{s<k} s^{-1}$ and Tajima's estimator $\widehat\pi_k$ computed on the $k$ copies satisfy

$$\mathbb E[\widehat\theta_{W,k}] \le \frac{k}{n}\,\theta_2, \qquad \mathbb E[\widehat\pi_k] \le \frac{k}{n}\,\theta_2 .$$

In particular, for a gene present in all genomes ($k = n$) but still subject to loss,

$$\mathbb E[\widehat\theta_{W,n}] = \theta_2\,\frac{\sum_{s=1}^{n-1}\frac{1}{s+\rho}}{\sum_{s=1}^{n-1}\frac{1}{s}} < \theta_2 .$$

So treating dispensable genes like core genes systematically underestimates the site mutation rate.

## Depends on

- [Gene frequency spectrum of the infinitely many genes model](gene-frequency-spectrum-of-the-infinitely-many-genes-model.md)

## Expansion

Conditioning on $F(u) = k$ selects genealogies in which the gene's subtree, gained at some ancestral point and thinned by losses, reaches exactly $k$ leaves; mutations fall on this subtree only, and the $s$-class counts the subtree's branches subtending $s$ leaves. Because the gene was gained more recently than the root, the subtree is shorter than the full genealogy of the $k$ carriers, which is why every class is deflated by at least the factor $k/n$. The factor $(j+1)/(j+1+\rho)$ is the probability, in the Hoppe-urn description of family sizes, that the gene survives the relevant coalescence step.

## Sources

- Franz Baumdicker, "The site frequency spectrum of dispensable genes", *Theoretical Population Biology* 100 (2015), 13–25, <https://doi.org/10.1016/j.tpb.2014.12.001>; preprint arXiv:1407.2488, <https://doi.org/10.48550/arXiv.1407.2488>. Numbering of the arXiv version: Theorem 1, Theorem 3, Corollary 3.5, Theorem 4, Corollary 4.1, Corollary 6.9.
