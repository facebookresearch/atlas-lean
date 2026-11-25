# Unweighted LD-score regression estimator of heritability

For natural numbers $N, M$, LD scores $\ell \in \mathbb{R}^M$ and statistics
$\chi \in \mathbb{R}^M$, the unweighted LD-score regression estimator of heritability is

$$
\hat h^2 = \frac{\hat b\, M}{N}, \qquad \hat b = \frac{S_{\ell\chi}}{S_{\ell\ell}}, \qquad
S_{xy} = \sum_{j=1}^{M} (x_j - \bar x)(y_j - \bar y),
$$

where $\hat b$ is the ordinary least-squares slope of $\chi$ on $\ell$ and $\bar x$ is the mean of
$x_1, \dots, x_M$. The estimator is meant for $N \ge 1$ and LD scores that are not all equal. With
the convention $x/0 = 0$, $\hat b = 0$ when the LD scores are all equal ($S_{\ell\ell} = 0$, where
the slope is not identified), and $\hat h^2 = 0$ when $N = 0$. It is an unweighted analogue of the
estimator of Bulik-Sullivan et al. (2015), who fit the slope by weighted least squares; for finite
samples the two slopes generally differ.

## Sources

- B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working Group of
  the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price, B. M. Neale, *LD Score
  regression distinguishes confounding from polygenicity in genome-wide association studies*, Nat.
  Genet. 47 (2015), 291–295.
