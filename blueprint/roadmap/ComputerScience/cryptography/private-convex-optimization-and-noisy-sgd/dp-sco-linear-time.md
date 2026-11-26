# Optimal private stochastic convex optimization in linear time

Under the assumptions of private stochastic convex optimization, there are $(\varepsilon,\delta)$-differentially private algorithms achieving the optimal excess population risk $\tilde O\big(LD(1/\sqrt{n} + \sqrt{d\log(1/\delta)}/(\varepsilon n))\big)$ with $O(\min\{n, n^2/d\})$ gradient computations, matching the running time of optimal non-private algorithms, compared with $O(\min\{n^{3/2}, n^{5/2}/d\})$ for earlier optimal private algorithms. One algorithm is one-pass noisy SGD with variable batch sizes, analyzed through privacy amplification by iteration; the other is **iterative localization**, which solves a sequence of increasingly regularized private ERM problems on disjoint batches, each localizing the optimum to a ball of geometrically shrinking radius.

## Proof sketch

For iterative localization, phase $k$ uses a fresh batch of size $n_k = n/2^k$, minimizes a $\lambda_k$-strongly-convex regularized objective centred at the previous output with a stable non-private method, and adds Gaussian noise calibrated to the stability $L/(\lambda_k n_k)$. Strong convexity makes the regularized minimizer stable, so its population risk is controlled, and the geometric decrease of the noise and the radius makes the total error dominated by the first phase while the total number of gradient evaluations is linear in $n$.

## Depends on

- [Private stochastic convex optimization has the non-private rate in the common regime](dp-sco-optimal-rate.md)

## Proof depends on

- [Private stochastic convex optimization has the non-private rate in the common regime](dp-sco-optimal-rate.md)

## Sources

- V. Feldman, T. Koren, K. Talwar, "Private Stochastic Convex Optimization: Optimal Rates in Linear Time", STOC (2020), arXiv:2005.04763.
