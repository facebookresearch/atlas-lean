# Optimal private stochastic convex optimization in linear time

Assume the setting of private stochastic convex optimization (convex feasible set of diameter $D$, losses convex and $L$-Lipschitz) and, in addition, that every loss $\ell(\cdot, z)$ is $\beta$-smooth with $\beta \le c\,(L/D)\min\{\sqrt n, \rho n/\sqrt d\}$ for a universal constant $c$. For every $\rho > 0$ there is an algorithm using $n$ gradient evaluations that is $(\alpha, \alpha\rho^2/2)$-Rényi differentially private for all $\alpha \ge 1$ (equivalently $\rho^2/2$-zCDP) and whose output has expected excess population risk $O\bigl(DL(1/\sqrt n + \sqrt d/(\rho n))\bigr)$. Choosing $\rho$ to give $(\varepsilon, \delta)$-differential privacy (valid when $\rho \le \ln(1/\delta)$) yields the optimal excess population risk $O\bigl(LD(1/\sqrt{n} + \sqrt{d\log(1/\delta)}/(\varepsilon n))\bigr)$ with $O(\min\{n, n^2/d\})$ gradient computations, matching the running time of optimal non-private algorithms, compared with $O(\min\{n^{3/2}, n^{5/2}/d\})$ for the earlier optimal private algorithm. The linear gradient complexity is claimed only under this smoothness assumption: for general (non-smooth) convex Lipschitz losses the localization approach with regularized ERM achieves the optimal rate with $O(n^2)$ gradient computations. One algorithm is one-pass noisy SGD with variable batch sizes, analyzed through privacy amplification by iteration; the other is **iterative localization**.

## Proof sketch

Iterative localization runs phases on disjoint batches of geometrically decreasing size. Each phase starts from the previous output, runs a non-private algorithm with small $\ell_2$-sensitivity and adds Gaussian noise calibrated to that sensitivity, which makes the phase private; the phase localizes an approximate minimizer to a ball whose radius (in mean square) shrinks by a constant factor. In the smooth case the inner algorithm is one-pass projected SGD with fixed step size $\eta \le 2/\beta$, whose iterates and their average have $\ell_2$-sensitivity at most $2L\eta$; this is where the smoothness bound enters. In the non-smooth case the inner algorithm minimizes a strongly convex regularized empirical objective, whose minimizer is stable, but solving it to the required accuracy costs $O(n^2)$ gradient computations overall. The geometric decrease of the noise and the radius makes the total error dominated by the first phase, while the total number of gradient evaluations stays linear in $n$ in the smooth case.

## Depends on

- [Private empirical risk minimization and private stochastic convex optimization](private-erm-and-sco.md)

## Proof depends on

- [Private stochastic convex optimization has the non-private rate in the common regime](dp-sco-optimal-rate.md)

## Sources

- V. Feldman, T. Koren, K. Talwar, "Private Stochastic Convex Optimization: Optimal Rates in Linear Time", STOC (2020), arXiv:2005.04763, abstract, Theorem 1.1, Lemmas 4.2 and 4.3 and Section 4.
