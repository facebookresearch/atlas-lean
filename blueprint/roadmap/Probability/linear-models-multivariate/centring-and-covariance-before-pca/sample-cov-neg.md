# Negating the data leaves the sample covariance unchanged

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, and write $S(Y)$ for the
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
of a data matrix $Y$. For every $n$, replacing every sample $x_i$ by $-x_i$ does not change the
sample covariance:

$$S(-X) = S(X).$$
