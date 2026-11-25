# Average spectral error of the randomized range finder

Let $A$ be a real $m \times n$ matrix with singular values $\sigma_1 \ge \sigma_2 \ge \cdots$ (with
$\sigma_j = 0$ for $j > \min\{m, n\}$). Choose $k \ge 2$ and $p \ge 2$ with $k + p \le \min\{m, n\}$, let
$\Omega$ be an $n \times (k + p)$ matrix with independent standard Gaussian entries, and let $P_Y$ be
the orthogonal projection onto the range of $Y = A\Omega$. Then, for the spectral norm,

$$\mathbb{E}\,\|(I - P_Y)A\| \le \left(1 + \sqrt{\frac{k}{p - 1}}\right)\sigma_{k+1} + \frac{e\sqrt{k + p}}{p}\Big(\sum_{j > k} \sigma_j^2\Big)^{1/2}.$$

## Idea

The best rank-$k$ error in the spectral norm is $\sigma_{k+1}$, attained by truncating the singular
value decomposition. The first term of the bound is within the factor $1 + \sqrt{k/(p - 1)}$ of that
optimum. The second term, the Frobenius tail of the singular values times $e\sqrt{k + p}/p$, is the
price of measuring the error in the spectral norm; it is small when the singular values beyond the
$k$-th decay quickly or when the oversampling $p$ is large.

## Statements

- [Average spectral error of the randomized range finder](integral-norm-residual-le.md)

## Background

- [Average Frobenius error of the randomized range finder](../frobenius-error/README.md): the algorithm, its Gaussian test matrix and its residual
