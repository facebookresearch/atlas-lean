# Allelic-test variance inflation under inbreeding

Let subjects $(X_i,Y_i)$ be iid, where $X_i\in\{0,1,2\}$ is allele count
and $Y_i$ is case status, independent of $X_i$ under the null.
Assume $\mathbb P(Y_i=1)=\rho\in(0,1)$, $p\in(0,1)$, $q=1-p$ and
$F\in[0,1]$. The probabilities for $X_i=2,1,0$ are respectively
$p^2+Fpq$, $2pq(1-F)$ and $q^2+Fpq$. Then

$$\mathbb E X_i=2p,\qquad \sigma^2=\operatorname{Var}X_i=2pq(1+F)>0.$$

For the first $N$ subjects, let $R,S$ be case/control counts,
$\bar X_1,\bar X_0$ the group means, $\hat p=\bar X/2$ and
$v_N=N^{-1}\sum_i(X_i-\bar X)^2$.
On nondegenerate tables define
$T_A=(\bar X_1-\bar X_0)^2/[2\hat p(1-\hat p)(1/R+1/S)]$.
The canonical [trend statistic](ca-stat.md) equals
$T_C=(\bar X_1-\bar X_0)^2/[v_N(1/R+1/S)]$.
Use the canonical zero convention when a denominator vanishes.
As $N\to\infty$,

$$T_C\Longrightarrow\chi^2_1,\qquad T_A\Longrightarrow(1+F)\chi^2_1.$$

Thus the ordinary chi-square reference is asymptotically anticonservative
for the allelic test when $F>0$. $F=0$ recovers asymptotic calibration,
not exact finite-sample calibration; $F=1$ doubles the limiting scale.
Monomorphic loci and constant genotype scores are excluded by the
positive-variance hypotheses, not treated as chi-square limits.

## Depends on

- [Cochran–Armitage statistic](ca-stat.md)

## Proof depends on

- [Canonical iid-subject chi-square limit](tendsto-in-distribution-ca-stat.md)

## Expansion

The two moments follow by summing the three genotype probabilities.
The [trend-test limit](tendsto-in-distribution-ca-stat.md) provides the limit of $T_C$.
The law of large numbers gives $R/N\to\rho$, $\hat p\to p$ and
$v_N\to\sigma^2$. Nondegenerate tables therefore have probability
approaching one. The exact relation
$T_A=[v_N/(2\hat p(1-\hat p))]T_C$ and Slutsky's theorem give the
allelic limit. The variance inflation is not caused by treating distinct
individuals as dependent; it is the within-individual allele covariance.

## Sources

- P. D. Sasieni, "From genotypes to genes: doubling the sample size", Biometrics 53 (1997), 1253–1261, <https://doi.org/10.2307/2533494> (the allelic test requires Hardy–Weinberg proportions). The variance is derived above.
