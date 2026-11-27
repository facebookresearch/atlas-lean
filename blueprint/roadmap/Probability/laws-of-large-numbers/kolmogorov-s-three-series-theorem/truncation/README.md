# Truncation of random variables

For real-valued functions $X_0, X_1, \dots$ on a set $\Omega$, a level $A \in \mathbb{R}$ and an index $n$, the truncation of $X_n$ at $A$ is the function $Y_n = X_n \mathbf{1}_{\{|X_n| \le A\}}$: $Y_n(\omega) = X_n(\omega)$ when $|X_n(\omega)| \le A$, and $Y_n(\omega) = 0$ otherwise. For $A < 0$ the truncation is identically zero.

## Idea

Truncation replaces a variable that may have no mean or variance by a bounded one: $|Y_n| \le |A|$, so for measurable $X_n$ and a finite measure $Y_n$ lies in every $L^p$ space, and on a probability space $|\mathbb{E}[Y_n]| \le |A|$ and $\operatorname{Var}(Y_n) \le A^2$. Since $Y_n$ is a fixed measurable function of $X_n$, truncation keeps measurability and independence. The price is the event $\{|X_n| > A\}$, where $Y_n$ and $X_n$ differ. When $\sum_n P(|X_n| > A) < \infty$, the first Borel–Cantelli lemma shows that almost surely $Y_n = X_n$ for all large $n$, so series and averages built from the truncations behave like those built from the variables themselves. This is the first step of Kolmogorov's three-series theorem and of many proofs of laws of large numbers.

## Statements

- [Truncation of a random variable](truncated-rv.md)
- [Scalar truncation function](truncation-fun.md): definition of scalar truncation, the main definition applied to the identity function
- [Formula for the truncated random variable](truncated-rv-apply.md): formula for the truncation
- [Truncation factors through scalar truncation](truncated-rv-eq-comp.md): basic property: truncation acts value by value
- [Scalar truncation fixes values within the cutoff](truncation-fun-eq-self-of-abs-le.md): basic property of scalar truncation
- [Scalar truncation vanishes beyond the cutoff](truncation-fun-eq-zero-of-abs-gt.md): basic property of scalar truncation
- [Scalar truncation preserves nonnegativity](truncation-fun-nonneg-of-nonneg.md): basic property of scalar truncation
- [Truncation fixes values within the cutoff](truncated-rv-eq-of-abs-le.md): basic property: values within the cutoff are kept
- [Truncation leaves a family bounded by the cutoff unchanged](truncated-rv-eq-of-bdd.md): basic property: bounded families are unchanged
- [Truncation vanishes outside the closed band](truncated-rv-eq-zero-of-abs-gt.md): basic property: values beyond the cutoff are removed
- [Truncation preserves nonnegativity](truncated-rv-nonneg-of-nonneg.md): basic property: nonnegativity is kept
- [Measurability of scalar truncation](measurable-truncation-fun.md): basic property: measurability
- [Truncation preserves measurability](measurable-truncated-rv.md): basic property: measurability
- [Measurability of a truncated random variable](measurable-truncated-rv-of-measurable.md): basic property: measurability
- [Truncation is bounded by a nonnegative cutoff](abs-truncated-rv-le.md): basic property: boundedness
- [Truncation is bounded by the absolute cutoff](abs-truncated-rv-le-abs.md): basic property: boundedness
- [Integrability of truncated random variables](integrable-truncated-rv.md): basic property: integrability
- [Truncated random variables lie in every Lp space](mem-lp-truncated-rv.md): basic property: every moment is finite
- [Mean bound for a truncated random variable](abs-integral-truncated-rv-le.md): basic property: bound on the mean
- [Variance bound for a truncated random variable](variance-truncated-rv-le.md): basic property: bound on the variance
- [Truncation preserves independence](i-indep-fun-truncated-rv.md): basic property: independence is kept
- [Truncations eventually agree with the variables](ae-eventually-truncation-eq.md): basic property: truncations eventually agree with the variables when the tail probabilities are summable
