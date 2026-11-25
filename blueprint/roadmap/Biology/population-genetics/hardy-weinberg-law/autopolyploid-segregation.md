# Autotetraploid chromosome segregation approaches binomial proportions

Use a deterministic biallelic autotetraploid model with no selection,
mutation or drift, equal gamete contribution from zygotes, random union of
diploid gametes, and random chromosome segregation with no double reduction.
Let $g=(g_0,g_1,g_2)$ be a probability vector for the number of counted
alleles in a gamete. Two independent gametes $X,Y$ form a zygote with
$K=X+Y$. From a zygote with $k\in\{0,\ldots,4\}$ counted copies, the
next gamete count is $j\in\{0,1,2\}$ with probability

$$T_{kj}=\frac{\binom{k}{j}\binom{4-k}{2-j}}6,$$

where out-of-range binomial coefficients are zero. Set
$g'_j=\sum_{k=0}^4(g*g)_kT_{kj}$. This is a probability vector,
$p=g_2+g_1/2$ is invariant, and

$$g'_2=\tfrac13g_2+\tfrac23p^2.$$

If $g_t$ is the iterated gamete law and
$g_* = ((1-p)^2,2p(1-p),p^2)$, then exactly

$$g_t-g_*=3^{-t}(g_0-g_*)$$

as vectors, where $g_0$ here denotes the initial gamete law. In particular
the second-copy and heterozygote deviations each have factor $3^{-t}$.
The zygote law at that cycle is $z_t=g_t*g_t$, and it converges to
$\operatorname{Binomial}(4,p)$. A precise geometric bound is

$$d_{\rm TV}(z_t,\operatorname{Binomial}(4,p))
 \le4\,|g_{2,0}-p^2|\,3^{-t},$$

where $d_{\rm TV}$ is half the finite $\ell^1$ distance. The zygote
error is not asserted to have exactly the same ratio in each generation:
convolution also contains a term of order $9^{-t}$.

## Background

- [Diploid Hardy-Weinberg proportions after one random union](offspring-apply.md)

## Expansion

The hypergeometric rows sum to one and have conditional mean $k/2$.
Since $\mathbb E K=4p$, the new gamete mean is $2p$, proving allele-frequency
invariance. Also

$$\mathbb E\binom K2
 =\mathbb E\binom X2+\mathbb E\binom Y2+\mathbb E[XY]
 =2g_2+4p^2,$$

so $g'_2=\mathbb E\binom K2/6$. Normalization and constant $p$ give the
other two coordinate recursions. If $d_t=g_{2,t}-p^2$, then
$g_t-g_*=(d_t,-2d_t,d_t)$ and $d_t=3^{-t}d_0$.
Convolution is an $\ell^1$ contraction against a probability vector, so
$\|g_t*g_t-g_* *g_*\|_1\le2\|g_t-g_*\|_1=8|d_t|$, proving the bound.

Unlike this diploid-gamete model, ordinary diploid random union gives
Hardy-Weinberg zygotes after one generation. That diploid result is a
comparison, not a proof prerequisite for the tetraploid recurrence.
Double reduction and other inheritance laws remain separate models.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, p. 240, "Other matrix approaches" before Section V.12, mentions Bartlett and Haldane's autotetraploid work in the context of regular inbreeding. That is historical context only: the random-union, no-double-reduction model and all its formulas are explicitly derived above.
