# Recursive least squares equals batch regularised least squares

For positive definite $P_0$,

$$\theta_t = \Big(P_0^{-1} + \sum_{k<t} \varphi_k \varphi_k^\top\Big)^{-1} \Big(P_0^{-1} \theta_0 + \sum_{k<t} y_{k+1} \varphi_k\Big),$$

the unique solution of the normal equations of
[RLS solves the regularised normal equations](rls-information-mul-vec-rls-fst.md): the recursion computes, with one
rank-one update per observation, the batch regularised least-squares estimate.
