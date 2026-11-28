# Scale-invariant Poisson structure of the IBD cluster of a locus

**Setting.** Let $\Pi_{eq}$ be a random partition of $\mathbb{R}_+$ distributed according to the invariant law of the half-line partitioning process (the ancestral recombination graph extended to a continuous chromosome) with recombination rate $1$; $x\sim_{\Pi_{eq}}y$ means that $x$ and $y$ lie in the same block, i.e. are inherited from the same ancestor (identical by descent). For $R>1$ define the random measure on $[0,1]$

$$
\vartheta^R[a,b]=\frac{1}{\log R}\int_{R^a}^{R^b}\mathbf 1_{\{x\sim_{\Pi_{eq}}0\}}\,dx,\qquad 0\le a\le b\le 1,
$$

which records, on a logarithmic scale of positions, the genetic material identical by descent with the locus $0$.

**Theorem.** Let $\mathcal P^\infty$ be a Poisson point process on $[0,1]\times\mathbb{R}_+$ with intensity $x^{-2}e^{-y/x}\,dx\,dy$ and set

$$
\vartheta^\infty=\sum_{(x_i,y_i)\in\mathcal P^\infty}y_i\,\delta_{x_i}.
$$

Then $\vartheta^R\Rightarrow\vartheta^\infty$ in distribution as $R\to\infty$, for the weak topology on locally finite measures on $[0,1]$. For disjoint intervals $[a_i,b_i]\subset[0,1]$ and integers $n_i\ge1$ the limit has the moments

$$
\mathbb{E}\Bigl[\prod_{i=1}^k\vartheta^\infty([a_i,b_i])^{n_i}\Bigr]=\prod_{i=1}^k n_i!\,b_i^{\,n_i-1}(b_i-a_i).
$$

The restriction $n_i\ge1$ matters: for $n_i=0$ the factor would be $(b_i-a_i)/b_i\ne1$, whereas $\vartheta^\infty([a,b])$ has an atom of mass $a/b$ at $0$ (its Laplace transform is $(1+sa)/(1+sb)$). In particular $\vartheta^\infty([0,x])$ is exponentially distributed with mean $x$: the rescaled length of the block containing $0$ over $[0,R^x]$ is asymptotically exponential.

## Depends on

- [Stationary law of the ancestral recombination graph under strong recombination](stationary-law-of-the-ancestral-recombination-graph-under-strong-recombination.md)

## Expansion

Projecting the intensity onto the first coordinate gives $\int_0^\infty x^{-2}e^{-y/x}\,dy=x^{-1}$, so the clusters of material identical by descent with $0$ are located, on the log scale, at the points of the scale-invariant Poisson process with intensity $dx/x$, and each cluster at log-position $x$ carries an exponential amount of material with mean $x$. Consequently the masses on disjoint log-intervals are independent and $\mathbb{E}[\vartheta^\infty([0,b])^n]=n!\,b^n$, the moments of an exponential law with mean $b$. The proof computes the moments of $\vartheta^R$ from the strong-recombination approximation $\mu^{\rho,z}(\pi)\approx F(\pi)/\rho^{k}$ of the finite-locus stationary law, integrated over the positions of $n$ loci on the log scale, and identifies the limits as the moments above, which determine the law.

## Sources

- Amaury Lambert, Verónica Miró Pina and Emmanuel Schertzer, "Chromosome painting: How recombination mixes ancestral colors", *Ann. Appl. Probab.* 31(2) (2021), 826–864. <https://doi.org/10.1214/20-AAP1606>
- Preprint version (the locators in this item follow its numbering): Amaury Lambert, Verónica Miró Pina, Emmanuel Schertzer, *Chromosome painting: how recombination mixes ancestral colors*, arXiv (2018). Theorem 1.5 and the remark following it; Lemma 5.1 (moments of the limit measure). <https://doi.org/10.48550/arXiv.1807.09116>
