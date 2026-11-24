# Power iteration converges to the dominant eigenvector up to sign

Under the hypotheses of the unnormalized bound, the power iterates
$v_k = T^k v_0 / \|T^k v_0\|$ satisfy $\|v_k - s_k q\| \le 2\rho^k \|v_0\|/|c|$ for some sign
$s_k = \pm 1$.

## Informally uses

- [Power iteration converges linearly (unnormalized form)](norm-smul-pow-apply-sub-le.md): the unnormalized bound.
- [Normalizing at most doubles the distance to a unit vector](norm-normalize-sub-le.md): normalization.

## Background

- [Principal component analysis](../../../Probability/linear-models-multivariate/principal-component-analysis/README.md): power iteration on a sample covariance matrix computes the first principal component.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 27 (convergence of power iteration).
