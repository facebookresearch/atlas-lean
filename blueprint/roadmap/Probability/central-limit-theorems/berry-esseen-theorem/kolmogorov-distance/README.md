# Kolmogorov distance to the normal law

For a measure $\mu$ on $\mathbb{R}$ and a positive integer $n$, the Kolmogorov error of $\mu$ at $n$ is
the real number

$$\sup_{x \in \mathbb{R}} \left|F_{\mu,n}(x) - \Phi(x)\right|,$$

where $\Phi$ is the standard normal distribution function and $F_{\mu,n}$ is the distribution function
of the normalized law of $\mu$ at $n$. When $\mu$ is a probability measure, that law is the law of
$(X_0 + \dots + X_{n-1})/\sqrt{n}$ for independent random variables $X_0, X_1, \dots$ with law $\mu$,
and $F_{\mu,n}(x)$ is the probability that this normalized sum is at most $x$. Otherwise, by
convention, the normalized law is the zero measure and $F_{\mu,n}$ is a fixed but unspecified
distribution function of some probability measure, not the zero function. Each value
$|F_{\mu,n}(x) - \Phi(x)|$ lies in $[0, 1]$, so the supremum is finite and lies in $[0, 1]$.

## Idea

The Kolmogorov distance between two laws on the real line is the largest vertical gap between their
distribution functions. Here it measures how far the normalized sum of $n$ independent copies of $\mu$
is from the standard normal law. When $\mu$ has mean $0$ and variance $1$, the central limit theorem
together with the continuity of $\Phi$ makes this distance tend to $0$. A bound on the Kolmogorov
error is the same thing as a bound on $|F_{\mu,n}(x) - \Phi(x)|$ holding for every $x$ at once, which
is the form in which Berry–Esseen bounds are stated and used. Example: if $\mu$ is the standard
Gaussian law, the normalized sum is again standard Gaussian, so the error is $0$; the card records the
case of one summand.

## Statements

- [Kolmogorov error](kolmogorov-error.md)
- [Standard normal CDF](normal-cdf.md): definition used in the main definition
- [Each CDF error is at most the Kolmogorov error](pointwise-le-kolmogorov-error.md): basic property: each pointwise error is bounded by the supremum
- [The CDF error is at most one](pointwise-error-le-one.md): basic property of the pointwise error, used for boundedness
- [The CDF errors are bounded above](error-range-bdd-above.md): lemma: the supremum defining the error is finite
- [The Kolmogorov error is nonnegative](kolmogorov-error-nonnegative.md): basic property
- [The Kolmogorov error is at most one](kolmogorov-error-le-one.md): basic property
- [Kolmogorov error bounds are uniform CDF bounds](error-le-iff.md): equivalent formulation as uniform CDF bounds
- [The Kolmogorov error vanishes for one standard Gaussian summand](standard-gaussian-error-one.md): example: zero error for one Gaussian summand

## Background

- [Normalized sums of a standardized i.i.d. model](../normalized-sums/README.md): the normalized law
  whose distribution function is compared with $\Phi$.
