# Purity maximizes the BDeu local score

Let a discrete variable $X$ with $r$ states have a parent set with $q$ joint instantiations in a Bayesian network, and let $s_{jk}$ be the number of data items in which the parents take instantiation $j$ and $X$ takes state $k$, with $M_j = \sum_k s_{jk}$. The Bayesian Dirichlet equivalent uniform (BDeu) local score with prior equivalent sample size $\alpha > 0$ is

$$S = \prod_{j=1}^q \frac{\Gamma(\alpha/q)}{\Gamma(\alpha/q + M_j)}\prod_{k=1}^r \frac{\Gamma\bigl(\alpha/(rq) + s_{jk}\bigr)}{\Gamma\bigl(\alpha/(rq)\bigr)}.$$

For fixed totals $M_1,\dots,M_q$, $S$ is maximized over all nonnegative integer arrays $(s_{jk})$ with row sums $M_j$ exactly when every row is pure, $s_{jk} = M_j$ for one $k$ and $0$ otherwise; the maximum value is

$$\prod_{j=1}^q \frac{\Gamma(\alpha/q)\,\Gamma\bigl(\alpha/(rq) + M_j\bigr)}{\Gamma(\alpha/q + M_j)\,\Gamma\bigl(\alpha/(rq)\bigr)} .$$

In a SNP pattern, where $X$ is disease status and the parents are SNPs, purity means that every joint genotype is observed only in cases or only in controls.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

For fixed $M_j$ the first factor of row $j$ is constant, and the second is $\exp\sum_k \bigl[\ln\Gamma(\beta + s_{jk}) - \ln\Gamma(\beta)\bigr]$ with $\beta = \alpha/(rq)$. Since $\ln\Gamma$ is convex, this is a convex function of $(s_{j1},\dots,s_{jr})$ on the simplex $\sum_k s_{jk} = M_j$, so it is maximized at a vertex, where one count equals $M_j$ and the empty states contribute factors $1$. The rows are independent, which gives the product.

## Sources

- X. Jiang and R. E. Neapolitan, "Mining pure, strict epistatic interactions from high-dimensional datasets: ameliorating the curse of dimensionality", PLoS ONE 7 (2012), e46771, <https://doi.org/10.1371/journal.pone.0046771>, PMCID PMC3470561. Eq. (2) and Theorem 1, a result of A. P. Singh and A. W. Moore (2005).
