# Bootstrap probability that the maximum is reproduced

For $n + 1$ distinct data values, a bootstrap sample of the same size reproduces the sample maximum, $X^*_{(n+1)} = X_{(n+1)}$, with conditional probability

$$P\{X^*_{(n+1)} = X_{(n+1)} \mid X_0, \dots, X_n\} = 1 - \Bigl(1 - \frac{1}{n+1}\Bigr)^{n+1} .$$

This is the [count of resamples that reproduce the maximum](card-resample-sup-eq.md) divided by $(n+1)^{n+1}$. On that event the bootstrap pivot $n(X_{(n)} - X^*_{(n)})$ is $0$.

## Informally uses

- [Resamples that reproduce the maximum](card-resample-sup-eq.md): the count.

## Sources

- P. J. Bickel and D. A. Freedman, "Some asymptotic theory for the bootstrap", *Ann. Statist.* 9 (1981) 1196–1217, Section 6, Counter-example 2.
