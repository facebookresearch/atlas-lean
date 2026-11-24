# A priori estimate of the population risk for two-layer ReLU networks

There is an absolute constant $C$ such that the following holds. Let $\log(2d) \ge 1$, $n \ge 1$
and $m \ge 1$; let $\rho_x$ be a probability measure carried by $X = [-1, 1]^d$; let $f^*$ be
measurable with values in $[0, 1]$ on $X$ and
$f^*(x) = \int a(w) \max(\langle w, x \rangle, 0) \, d\pi(w)$ on $X$, for a probability measure
$\pi$ carried by the $\ell^1$ unit sphere and a function $a$ with $\int a^2 \, d\pi \le \gamma^2$,
$\gamma \ge 0$. Let $\lambda \ge 4 \sqrt{2 \log(2d) / n}$ and $\delta > 0$. Then with probability
at least $1 - \delta$ over an i.i.d. sample $x_1, \dots, x_n \sim \rho_x$, every minimizer
$\hat\theta$ over width-$m$ networks $f(x; \theta) = \sum_k a_k \max(\langle w_k, x \rangle, 0)$
of the regularized empirical risk

$$J_\lambda(\theta) = \frac1n \sum_{i=1}^n \tfrac12 \big(T f(x_i; \theta) - f^*(x_i)\big)^2 + \lambda \big(\lVert \theta \rVert_P + 1\big),
\qquad T t = \max(\min(t, 1), 0),$$

satisfies

$$\mathbb{E}_{x \sim \rho_x} \big|T f(x; \hat\theta) - f^*(x)\big|^2 \le C \Big( \frac{\gamma^2}{m} + \lambda \max(1, \gamma) + \frac{\max(1, \gamma) + \sqrt{\log(n / \delta)}}{\sqrt n} \Big).$$

Taking the infimum over representations gives the source's form with $\gamma_2(f^*)$, the Barron
norm of $f^*$ in the source's normalization (no bias, data in $[-1, 1]^d$). The bound is a priori
(it involves only the norm of the target), and its estimation part does not depend on the width:
with $\lambda \asymp \lambda_n$ and $m \ge \sqrt n$ it is $O(n^{-1/2})$ up to logarithms, in the
over-parametrized regime included. Measurability of $f^*$ is an added regularity assumption
(on $X$ the representation already makes $f^*$ continuous). As in the
[Rademacher risk bound](../../generalization-bounds-and-concentration/rademacher-complexity/risk-le-empirical-add-rademacher.md),
"with probability at least $1 - \delta$" is stated with the outer measure of the product measure,
since the event need not be measurable.

## Informally uses

- [Direct approximation theorem for the Barron space](barron-direct-approximation.md): the source's proof compares $\hat\theta$ with the network of Theorem 3.1, whose path norm is at most $2 \gamma_2(f^*)$ independently of $m$.
- [Rademacher complexity of path-norm balls of two-layer ReLU networks](rademacher-complexity-path-norm-ball-val.md): the bound (5.1), which with a union bound over path-norm shells gives the a posteriori generalization bound (Theorem 5.2) used in the proof.

## Background

- [The Rademacher risk bound](../../generalization-bounds-and-concentration/rademacher-complexity/risk-le-empirical-add-rademacher.md): a one-sided version of the uniform deviation bound that the source cites as its Theorem 5.1 to turn Rademacher complexity into a generalization gap.

## Sources

- W. E, C. Ma and L. Wu, *A priori estimates of the population risk for two-layer neural networks*, Commun. Math. Sci. 17 (2019), Theorem 4.1 (noiseless case), with the setting of §3 (equations (3.1)–(3.4), Definition 3.1) and the proof in §5 (Theorem 5.1, bound (5.1), Theorem 5.2, Proposition 5.1).
