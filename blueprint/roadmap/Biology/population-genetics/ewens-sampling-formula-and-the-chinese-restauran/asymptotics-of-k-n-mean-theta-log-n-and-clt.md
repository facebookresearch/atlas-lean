# Bernoulli representation and central limit theorem for Ewens block counts

Fix $\theta>0$ and realize one **nested** Chinese restaurant process by
successive independent uniform choices: after $n$ customers, the next
customer starts a new block with probability $\theta/(n+\theta)$ and
joins a given size-$m$ block with probability $m/(n+\theta)$.
The partitions restrict consistently to earlier customers, and their
finite marginal laws are the canonical [CRP laws](../../../Probability/bayesian-statistics/blackwell-macqueen-urn/crp.md).
The choice construction is needed when discussing joint or almost-sure
claims, rather than merely a sequence of finite marginal measures.

For the number $K_n$ of blocks,

$$K_n=\sum_{i=0}^{n-1}\xi_i,\qquad
 \xi_i\ \text{independent Bernoulli}\left(\frac{\theta}{\theta+i}\right).$$

In particular $\xi_0=1$. As $n\to\infty$ with $\theta$ fixed,
$\mathbb E K_n=\theta\log n+O(1)$,
$\operatorname{Var}K_n=\theta\log n+O(1)$, and

$$\frac{K_n-\theta\log n}{\sqrt{\theta\log n}}
 \ \Longrightarrow\ \mathcal N(0,1).$$

## Depends on

- [Chinese restaurant finite marginal laws](../../../Probability/bayesian-statistics/blackwell-macqueen-urn/crp.md)

## Proof depends on

- [Lindeberg–Feller theorem for triangular arrays](../../../Probability/central-limit-theorems/lindeberg-feller-central-limit-theorem/lindeberg-feller-clt-triangular.md)

## Background

- [Exact number-of-alleles law](../../detecting-selection/ewens-watterson-test/num-alleles-prob-eq.md)

## Expansion

The conditional new-block probability given the entire seating past is
the deterministic number $\theta/(n+\theta)$; iterated conditioning
therefore factors every joint law of the indicators. Integral comparison
of $\sum_{i<n}\theta/(\theta+i)$ with a logarithm gives the mean estimate.
The variance is the same sum minus $\sum_{i<n}(\theta/(\theta+i))^2$,
and the latter sum is uniformly bounded.
For $n\ge2$ write $s_n^2=\operatorname{Var}K_n>0$ and normalize row
$i<n$ by $X_{n,i}=(\xi_i-\mathbb E\xi_i)/s_n$.
The row variance is one and $|X_{n,i}|\le1/s_n\to0$, so for every
positive Lindeberg threshold the entire truncated second-moment sum is
zero eventually. The linked theorem applies. Replacing the exact mean
and variance by the logarithmic asymptotics does not change the limit.
A finite initial row with zero variance can be defined as zero and is
irrelevant to this asymptotic argument.

## Sources

- N. Berestycki, *Recent progress in coalescent theory* (2009), <https://arxiv.org/abs/0909.3985>, Section 1.3.1, equation (8). The explicit nested construction, independence and triangular-array argument are given above.
