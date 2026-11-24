# Kurtz's pathwise estimate for a stochastic reaction network

(Kurtz 1970; Ethier–Kurtz 1986, ch. 11, proof of Thm 2.1.)

Let $C$ be a
[stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) on
a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) $G$ with finite
species set $S$, finite reaction set $\rho$ and propensities $\lambda_r$, and let $N \ge 1$. Let $X$
satisfy the [random time-change equations](is-chain-path.md) of $C$ driven by functions
$y_r \colon [0, \infty) \to \mathbb{N}$, and let $x$ be a
[solution of the mean-field equation](is-solution.md) $x' = \sum_r \beta_r(x)\, \zeta_r$ of $G$ on
$t \ge 0$, for real functions $\beta_r$. Write $D(t) = \|X(t)/N - x(t)\|_1$ for the
[deviation](deviation.md) and $Z = \sum_r \|\zeta_r\|_1$ for the
[sum of the ℓ¹ norms of the reaction vectors](stoich-norm.md). Let $T, L, \eta, e, B \ge 0$ and
$\delta$ real, and suppose that:

- each function $s \mapsto \beta_r(x(s))$ is continuous on $[0, T]$;
- on the $\delta$-tube around $x$ over $[0, T]$ the scaled propensities are close to $\beta$ and
  bounded by $B$: for every reaction $r$, every $s \in [0, T]$ and every count vector
  $z \in \mathbb{N}^S$ with $\|z/N - x(s)\|_1 < \delta$,
  $|\lambda_r(z)/N - \beta_r(x(s))| \le e + L \|z/N - x(s)\|_1$ and $\lambda_r(z)/N \le B$;
- the scaled driving functions stay within $\eta$ of the identity: $|y_r(N a)/N - a| \le \eta$ for
  every reaction $r$ and every $a \in [0, (B + 1) T]$.

Let $A = D(0) + Z (\eta + e T)$. If $A e^{L Z T} + 2 \eta Z < \delta$, then for every
$t \in [0, T]$,

$$\left\|X(t)/N - x(t)\right\|_1 \le A\, e^{L Z t}.$$

The tube conditions bear on every count vector in the tube, not only on the values of the path.
Nothing is assumed of the $y_r$ besides the clock bound, and no right-continuity of $X$ is needed:
the clock bound itself limits the size of a jump.

Proof: let $t_0$ be the supremum of the times $t \in [0, T]$ such that $D < \delta$ on $[0, t)$. The
[Gronwall bound](deviation-le-of-tube.md) gives $D(t) \le A e^{L Z t}$ on $[0, t_0]$. If $t_0 < T$,
the path [stays in the tube a little longer](exists-tube-right.md), since the clock bound limits its
jumps and the clocks and $x$ are continuous; this contradicts the choice of $t_0$.
