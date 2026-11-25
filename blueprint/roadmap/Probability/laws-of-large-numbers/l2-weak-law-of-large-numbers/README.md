# L² weak law of large numbers

If $X_1, X_2, \dots$ are uncorrelated square-integrable random variables with common mean $\mu$ and variances
bounded by a constant, then the averages $S_n / n = (X_1 + \dots + X_n)/n$ converge to $\mu$ in mean square,
$E(S_n / n - \mu)^2 \to 0$, and hence in probability.

## Idea

Uncorrelated random variables add their variances, so $\operatorname{var}(S_n / n) \le C / n$, and Chebyshev's
inequality turns this into $P(|S_n / n - \mu| \ge \varepsilon) \le C / (n \varepsilon^2)$. The main case is that of
independent, identically distributed random variables with finite variance. For independent, identically distributed
variables a finite mean suffices: the weak law holds under $E|X_i| < \infty$ alone, and the strong law of large numbers
gives almost sure convergence. The variance of the sample mean card computes $\operatorname{var}(S_n / n)$ exactly for
independent, identically distributed variables.

## Statements

- [L² weak law of large numbers](l2-weak-law.md)

## Background

- [Expected value](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/README.md): expected values
- [Variance of the sample mean](../variance-of-the-sample-mean/README.md): the variance of the sample mean
- [Variance of a finite sum](../../moments/variance-of-a-finite-sum/README.md): the variance of a sum
- [Chebyshev's inequality](../../moments/chebyshev-s-inequality/README.md): deviations bounded by the variance
