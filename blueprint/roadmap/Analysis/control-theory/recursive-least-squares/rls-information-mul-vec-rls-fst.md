# RLS solves the regularised normal equations

For positive definite $P_0$, the RLS estimate satisfies

$$\Big(P_0^{-1} + \sum_{k<t} \varphi_k \varphi_k^\top\Big) \theta_t = P_0^{-1} \theta_0 + \sum_{k<t} y_{k+1} \varphi_k,$$

the normal equations of the batch problem of minimising
$(\theta - \theta_0)^\top P_0^{-1} (\theta - \theta_0) + \sum_{k<t} (y_{k+1} - \varphi_k^\top \theta)^2$.

## Background

- [Least squares and the normal equations](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/rss-le-iff-normal.md): minimisers of a residual sum of squares are
  exactly the solutions of its normal equations; the regularised problem here adds the positive definite quadratic
  penalty $(\theta - \theta_0)^\top P_0^{-1} (\theta - \theta_0)$.
