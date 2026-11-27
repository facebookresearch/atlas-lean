# Many-locus variance components and the covariance of relatives

Let $L\ge1$ and, for each locus $k\in\{1,\dots,L\}$, let $\mathcal A_k$ be a finite allele set with allele frequencies $p_k$. An individual's genotype is $g=((x_1,y_1),\dots,(x_L,y_L))$, with $x_k$ its maternal and $y_k$ its paternal allele at locus $k$. Assume Hardy–Weinberg proportions at every locus and linkage equilibrium in the strong sense that the $2L$ alleles $x_1,y_1,\dots,x_L,y_L$ are independent, with $x_k$ and $y_k$ distributed as $p_k$. Let $G=\gamma(g)$ be a genotypic value, where $\gamma$ is real valued and symmetric in $(x_k,y_k)$ at each locus but otherwise arbitrary (arbitrary epistasis), and put $\mu=\mathbb E G$.

At one locus, the symmetric functions of $(x_k,y_k)$ split orthogonally in $L^2$ into the constants, the additive functions $\alpha(x_k)+\alpha(y_k)$ with $\mathbb E\,\alpha(x_k)=0$, and the dominance functions $\delta(x_k,y_k)$ with $\mathbb E[\delta\mid x_k]=\mathbb E[\delta\mid y_k]=0$. For each labelling $c:\{1,\dots,L\}\to\{0,\mathrm A,\mathrm D\}$, let $H_c$ be the span of the products $\prod_k\phi_k$ in which $\phi_k$ is constant, additive or dominance at locus $k$ according as $c(k)=0,\mathrm A,\mathrm D$. Then the spaces $H_c$ are mutually orthogonal and together span all symmetric functions of $g$. Writing $G_c$ for the orthogonal projection of $G$ on $H_c$ and

$$V_{ij}=\sum_{c:\ |c^{-1}(\mathrm A)|=i,\ |c^{-1}(\mathrm D)|=j}\operatorname{Var}(G_c)\qquad(\text{also written }V_{A^iD^j}),$$

one has

$$G=\mu+\sum_{c\ne0}G_c,\qquad\operatorname{Var}G=\sum_{i+j\ge1}V_{ij},$$

with $V_{ij}=0$ whenever $i+j>L$. In particular $(L,V)$ are [Cockerham–Kempthorne components](../../quantitative-genetics/covariance-between-relatives/cockerham-components.md).

Now let $X$ and $Y$ be two non-inbred relatives in this population: each genotype has the law above; at every locus the number of alleles of $X$ identical by descent with alleles of $Y$ is $0$, $1$ or $2$ with probabilities $k_0,k_1,k_2$, the same at every locus; the identity states at distinct loci are independent (unlinked loci); and, given the identity states, alleles that are not identical by descent are independent draws from $p_k$. Put $2\varphi=k_1/2+k_2$ (twice the kinship coefficient) and $\Delta=k_2$. Then

$$\operatorname{Cov}(G_X,G_Y)=\sum_{i+j\ge1}(2\varphi)^i\,\Delta^j\,V_{ij},$$

that is, the covariance is the [Cockerham form](../../quantitative-genetics/covariance-between-relatives/cov.md) $\mathrm{Cov}(2\varphi,\Delta)$ of these components. For $L=1$ this is the [single-locus covariance between relatives in Cockerham form](../../quantitative-genetics/covariance-between-relatives/rel-cov-eq-cov.md); for parent and offspring ($k_1=1$) it gives $\sum_{i\ge1}2^{-i}V_{i0}$, whose one-locus case is the [parent–offspring covariance](../../quantitative-genetics/fisher-s-decomposition-of-genetic-variance/cov-parent-offspring-eq.md) $V_A/2$.

## Depends on

- [Cockerham–Kempthorne variance components](../../quantitative-genetics/covariance-between-relatives/cockerham-components.md)
- [Genetic covariance of relatives in Cockerham form](../../quantitative-genetics/covariance-between-relatives/cov.md)

## Proof depends on

- [Parent–offspring covariance is half the additive variance](../../quantitative-genetics/fisher-s-decomposition-of-genetic-variance/cov-parent-offspring-eq.md)
- [Single-locus covariance between relatives in Cockerham form](../../quantitative-genetics/covariance-between-relatives/rel-cov-eq-cov.md)
- [Multi-allelic linkage disequilibria after $t$ generations](linkage-diseq-iterate-2.md)

## Expansion

A full proof establishes the one-locus orthogonal decomposition, takes tensor products using the independence of the $2L$ alleles, and computes the covariance of two components: $\operatorname{Cov}(G_{c,X},G_{c',Y})=0$ for $c\ne c'$, and for $c=c'$ the covariance factors over loci, contributing $k_1/2+k_2$ at an additive locus, $k_2$ at a dominance locus and $1$ at a constant locus. It should also

- compute the two-locus additive-by-additive case explicitly, showing that its contribution is $(2\varphi)^2V_{20}$;
- construct the Cockerham–Kempthorne components from the genotype model above, so that the many-locus Cockerham form becomes a theorem rather than a hypothesis on the components.

## Sources

- C. C. Cockerham, *Partitioning hereditary variance with epistasis* (1954), and O. Kempthorne, *The correlation between relatives in a random mating population* (1954), Cockerham 1954; Kempthorne 1954, as cited.
- D. S. Falconer and T. F. C. Mackay, *Introduction to Quantitative Genetics*, 4th ed., 1996, variance components.
