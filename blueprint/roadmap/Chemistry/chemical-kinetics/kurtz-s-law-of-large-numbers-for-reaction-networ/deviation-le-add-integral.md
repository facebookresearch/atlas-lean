# Integral inequality for the deviation inside the tube

Let $C$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) on
a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) $G$ with finite
species set $S$, finite reaction set $\rho$ and propensities $\lambda_r$, and let $N \ge 1$. Let $X$
satisfy the [random time-change equations](is-chain-path.md) of $C$ driven by functions
$y_r \colon [0, \infty) \to \mathbb{N}$, and let $x$ be a
[solution of the mean-field equation](is-solution.md) $x' = \sum_r \beta_r(x)\, \zeta_r$ of $G$ on
$t \ge 0$, for real functions $\beta_r$. Write $D(s) = \|X(s)/N - x(s)\|_1$ for the
[deviation](deviation.md) and $Z = \sum_r \|\zeta_r\|_1$ for the
[sum of the ℓ¹ norms of the reaction vectors](stoich-norm.md). Let $T$, $\delta$, $L$ and $\eta$ be
real and $e, B \ge 0$, and suppose that:

- each function $s \mapsto \beta_r(x(s))$ is continuous on $[0, T]$;
- for every reaction $r$, every $s \in [0, T]$ and every count vector $z \in \mathbb{N}^S$ in the
  $\delta$-tube, $\|z/N - x(s)\|_1 < \delta$, the scaled propensity satisfies
  $|\lambda_r(z)/N - \beta_r(x(s))| \le e + L \|z/N - x(s)\|_1$ and $\lambda_r(z)/N \le B$;
- $|y_r(N a)/N - a| \le \eta$ for every reaction $r$ and every $a \in [0, (B + 1) T]$.

Let $t \in [0, T]$ be a time such that $D(s) < \delta$ for every $s \in [0, t)$ and $D$ is
integrable on $[0, t]$. Then

$$D(t) \le D(0) + Z (\eta + e T) + L Z \int_0^t D(s)\, ds.$$

The tube conditions bear on every count vector in the tube, not only on the values of the path.
