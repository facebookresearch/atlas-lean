# Mixed Poisson distributions

Let $\nu$ be a measure on $\mathbb{R}$, the mixing law of the rate. The mixed Poisson mass function gives $k \in \mathbb{N}$ the value

$$p_\nu(k) = \int e^{-r} \frac{r^k}{k!} \, d\nu(r),$$

an integral of a non-integrable function being read as $0$. When $\nu$ is a probability measure concentrated on $[0, \infty)$, $p_\nu$ is a probability mass function on $\mathbb{N}$: the law of a count $N$ that, given $\Lambda$, is Poisson with mean $\Lambda$, where $\Lambda$ has law $\nu$.

## Idea

Counts from a population whose members have different rates, such as accidents per driver or sequencing reads per gene, are not Poisson: drawing the rate at random before drawing the count adds variability. A mixed Poisson law has mean $\mathbb{E}\Lambda$ and, when $\Lambda$ has a second moment, variance $\mathbb{E}\Lambda + \operatorname{Var}\Lambda$: Poisson noise plus the spread of the rate, so the variance exceeds the mean unless the rate is almost surely constant. When $\Lambda$ has a finite mean, Jensen's inequality shows that the mass at zero, $\mathbb{E} e^{-\Lambda}$, is at least $e^{-\mathbb{E}\Lambda}$, the mass at zero of the Poisson law with the same mean. A point mass $\nu = \delta_\lambda$ gives back the Poisson law with mean $\lambda$, and a gamma mixing law gives the negative binomial law.

## Statements

- [Mixed Poisson mass function](poisson-mixture-real.md)
- [Nonnegativity of the mixed Poisson mass function](poisson-mixture-real-nonneg.md): basic property: nonnegativity
- [Normalization of a mixed Poisson law](has-sum-poisson-mixture-real.md): basic property: normalisation
- [Poisson mixture over a point mass is Poisson](poisson-mixture-real-dirac.md): special case: point mixing gives Poisson
- [Zero class of a mixed Poisson law](poisson-mixture-real-zero.md): basic property: mass at zero
- [Mean of a mixed Poisson law](has-sum-mul-poisson-mixture-real.md): basic property: the mean
- [Second factorial moment of a mixed Poisson law](has-sum-mul-sub-one-poisson-mixture-real.md): basic property: the second factorial moment
- [Second moment of a mixed Poisson law](has-sum-sq-poisson-mixture-real.md): basic property: the second moment
- [Variance decomposition of a mixed Poisson law](variance-poisson-mixture.md): basic property: variance decomposition
- [Squared coefficient of variation of a mixed Poisson law](cv-sq-poisson-mixture.md): basic property: squared coefficient of variation
- [Fano factor of the Poisson law](fano-poisson.md): special case: Poisson Fano factor
- [Zero inflation by mixing](exp-neg-integral-le-poisson-mixture-real.md): zero inflation by mixing
