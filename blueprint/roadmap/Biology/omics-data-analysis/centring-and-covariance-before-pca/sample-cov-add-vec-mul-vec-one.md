# Sample covariance is invariant under a common shift of all samples

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, and write $S(Y)$ for the
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
$(n-1)^{-1} Y_c^\top Y_c$ of a data matrix $Y$ with centred matrix $Y_c$. For every $n$ and every
$c \in \mathbb{R}^p$, adding $c$ to every sample leaves the sample covariance unchanged:

$$S(X + \mathbf 1 c^\top) = S(X),$$

where $\mathbf 1 \in \mathbb{R}^n$ is the all-ones vector. The
[uncentred second-moment matrix](second-moment.md) $\frac1n X^\top X$ is not invariant under such
shifts in general.
