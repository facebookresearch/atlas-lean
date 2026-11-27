# Expected abnormal-protein load under error-prone protein synthesis

A cell has $K$ genes; gene $i$ encodes $n_i$ amino acids and $y_i$ functional copies of its protein are needed per cell cycle. Each codon is synthesized wrongly, producing a nonfunctional protein, independently with probability $u\in(0,1)$, the phenotypic mutation rate. The gene is expressed until $y_i$ functional proteins exist. Then the number $x_i$ of nonfunctional proteins of gene $i$ made along the way is negative binomial: the number of failures before the $y_i$-th success in trials with success probability $(1-u)^{n_i}$. Hence

$$\mathbb E\,x_i=y_i\,\frac{1-(1-u)^{n_i}}{(1-u)^{n_i}},\qquad \bar x=\sum_i n_i\,\mathbb E\,x_i=\sum_i n_i y_i\bigl[(1-u)^{-n_i}-1\bigr],$$

where $\bar x$ is the expected number of amino acids spent on abnormal proteins. Moreover:

1. $\bar x\ge u\sum_i n_i^2y_i$ for all $u\in(0,1)$, with $\bar x=u\sum_i n_i^2y_i+O(u^2)$ as $u\to0$; the linear approximation is accurate while $u\,n_i\ll1$ for the genes carrying most of the weight $n_i^2y_i$.
2. $\bar x$ is increasing and convex in $u$ and grows without bound as $u\to1$, faster than any polynomial once $u\,n_i$ is of order one for the long, highly expressed genes.

## Depends on

- [Negative binomial mass function with real shape](../../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-pmf.md)
- [Mean of the negative binomial law](../../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/has-sum-mul-neg-binomial-real.md)

## Expansion

The negative binomial mean is $y(1-q)/q$ with $q=(1-u)^{n_i}$. For item 1, $(1-u)^{-n}\ge(1+u)^n\ge1+nu$ by $1/(1-u)\ge1+u$ and Bernoulli's inequality, and the first-order term of $(1-u)^{-n}$ is $nu$. Item 2 follows because each $(1-u)^{-n_i}$ is convex and increasing on $(0,1)$. With yeast protein lengths and abundances, the source finds the linear approximation becomes inaccurate for $u>5\times10^{-4}$ and $\bar x$ then rises steeply, which caps the phenotypic mutation rate that can evolve even when abnormal proteins are cheap. Splitting $n_i\mathbb E x_i$ into length $n_i$, expression $y_i$ and the per-functional-protein failure factor shows that the unevenness of the load across genes is driven mainly by expression level. Inverting the formula, a fraction of 15% to 35% of newly made proteins being nonfunctional corresponds in the source's yeast parameterization to $2.4\times10^{-4}$ to $6.1\times10^{-4}$ deleterious substitutions per codon.

## Sources

- M. Willensdorfer, R. Bürger and M. A. Nowak, "Phenotypic mutation rates and the abundance of abnormal proteins in yeast", PLoS Computational Biology 3 (2007), e203, Results ("The Model", Equations (7) and (8); "Components of $\bar x$") and Discussion, <https://doi.org/10.1371/journal.pcbi.0030203> (PMC2082502).
