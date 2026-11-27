# L² weak law of large numbers

Let $X_1, X_2, \dots$ be real random variables with $EX_i^2 < \infty$ that are uncorrelated, meaning
$E(X_i X_j) = EX_i \, EX_j$ whenever $i \ne j$, with $EX_i = \mu$ and $\operatorname{var}(X_i) \le C < \infty$ for all $i$.
Let $S_n = X_1 + \dots + X_n$. Then $S_n / n \to \mu$ in $L^2$, that is, $E(S_n / n - \mu)^2 \to 0$, and in
probability, as $n \to \infty$.

## Proof

The variance of a sum of square-integrable random variables is the sum of their covariances. For $i \ne j$, $X_i X_j$ is
integrable, since $|X_i X_j| \le (X_i^2 + X_j^2)/2$, and
$\operatorname{cov}(X_i, X_j) = E\big((X_i - EX_i)(X_j - EX_j)\big) = E(X_i X_j) - EX_i \, EX_j = 0$, by linearity of
the expected value and since a constant $c$ has expected value $c$. By linearity again, $E(S_n / n) = \mu$ and
$\operatorname{var}(S_n / n) = \operatorname{var}(S_n) / n^2$, so
$E(S_n / n - \mu)^2 = \operatorname{var}(S_n) / n^2 \le nC / n^2 = C / n \to 0$. The average $S_n / n$ is
square-integrable, by the triangle inequality for the $L^2$ seminorm, so for $\varepsilon > 0$ Chebyshev's inequality
gives $P(|S_n / n - \mu| \ge \varepsilon) \le \varepsilon^{-2} E(S_n / n - \mu)^2 \to 0$.

## Depends on

- [Expected value of a random variable](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)
- [Probability measure](../../foundations/probability-measures/is-probability-measure.md)

## Proof depends on

- [Variance of a finite sum](../../moments/variance-of-a-finite-sum/variance-sum.md)
- [Chebyshev's inequality](../../moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)
- [Monotonicity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Additivity and positive homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-nonnegative-additive-homogeneous.md)
- [Additivity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)
- [Triangle inequality for the $L^p$ seminorm](../../../MeasureTheory/lp-spaces/triangle-inequality-for-lp-seminorms/e-lp-norm-add-le.md)
- [Integral of a constant](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-const.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 2.2.1 (uncorrelated random variables) and Theorem 2.2.3 (version read: the author's January 2019 PDF).
