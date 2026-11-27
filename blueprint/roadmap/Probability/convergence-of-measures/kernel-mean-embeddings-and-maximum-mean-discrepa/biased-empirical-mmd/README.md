# Biased empirical MMD

Let $H$ be a real reproducing kernel Hilbert space of functions on a set $X$. For nonempty samples
$x_1, \dots, x_m$ and $y_1, \dots, y_n$ in $X$, the biased empirical maximum mean discrepancy is

$$\mathrm{MMD}_b = \sup_{\|f\|_H \le 1} \Big(\frac{1}{m} \sum_{i=1}^m f(x_i) - \frac{1}{n} \sum_{j=1}^n f(y_j)\Big).$$

## Idea

The plug-in estimate of the maximum mean discrepancy replaces the two laws by the empirical measures
of two lists of points. It is defined for any two nonempty lists, random or not, single points
included. By the reproducing property the expression in the supremum is the inner product of $f$ with
the difference of the empirical mean embeddings $\mu_X = \frac1m \sum_i \varphi(x_i)$ and $\mu_Y$, so by
the Cauchy–Schwarz inequality $\mathrm{MMD}_b = \|\mu_X - \mu_Y\|$, attained at the normalised difference
when it is nonzero. Expanding the square with the reproducing property gives a V-statistic in the
kernel values, diagonal terms $k(x_i, x_i)$ and $k(y_j, y_j)$ included. When the lists are independent
i.i.d. samples from laws $P$ and $Q$ and the expectations involved exist (finite second moments of the
norm of the feature map under $P$ and $Q$ suffice), these diagonal terms make $\mathrm{MMD}_b^2$ a
generally biased estimate of $\mathrm{MMD}(P, Q)^2$. For such samples of sizes $m, n \ge 2$, with the
feature map Bochner integrable under $P$ and under $Q$, omitting the within-sample diagonal terms and
averaging each within-sample sum over its $m(m-1)$ or $n(n-1)$ ordered pairs of distinct indices, while
the cross term keeps its denominator $mn$, gives the unbiased U-statistic; merely deleting the diagonal
terms does not (for the constant kernel $1$ and $m = n = 2$ it would give $-1$ instead of $0$).

## Statements

- [Biased empirical MMD](mmd-biased.md)
- [The biased empirical MMD is the distance between empirical mean embeddings](mmd-biased-eq.md): characterisation: the distance between the empirical mean embeddings
- [The biased empirical MMD as a V-statistic](mmd-biased-sq-eq.md): the square as a V-statistic in the kernel values
- [Empirical mean embedding](empirical-embedding.md): definition used in the characterisation
- [Reproducing property of the empirical mean embedding](inner-empirical-embedding.md): lemma used for the characterisation
- [Inner product of empirical mean embeddings](inner-empirical-embedding-empirical-embe.md): lemma used for the V-statistic form

## Background

- [Canonical feature map of a reproducing kernel Hilbert space](../reproducing-kernel/README.md): the feature map and the kernel
- [Maximum mean discrepancy](../maximum-mean-discrepancy/README.md): the population quantity, whose supremum is attained in the same way
