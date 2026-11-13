# Gauss–Markov covariance minimality

Let $X$ be a real $m \times n$ matrix such that
$X^\top X$ is invertible, and let $B = (X^\top X)^{-1} X^\top$. Then $BX = I_n$, and for every
real $n \times m$ matrix $A$ with $AX = I_n$ the matrix $AA^\top - BB^\top$ is positive
semidefinite.

In the linear model $y = X\beta + \varepsilon$ whose noise has identity covariance, $By$ is the
least-squares estimator of $\beta$, the estimators $Ay$ with $AX = I_n$ are exactly the linear
unbiased ones, and $AA^\top$ is the covariance of $Ay$.

## Sources

- C. F. Gauss, *Theoria combinationis observationum erroribus minimis obnoxiae* (1823); A. C. Aitken, “On Least Squares and Linear Combination of Observations,” *Proceedings of the Royal Society of Edinburgh* 55 (1936), 42–48, DOI `10.1017/S0370164600014346`.
