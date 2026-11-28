# Normalized complex error past the initial layer

For standard data and every enzyme level $e_0 > 0$, the scaled complex $c/e_0$ of a global Michaelis–Menten solution stays within $C\varepsilon$ of the slow manifold evaluated at the reduced solution, uniformly in slow time $\theta \in [\delta, T]$, with an explicit $C$ that does not depend on $e_0$.

Let $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$, $s_0 > 0$, $\delta > 0$ and $T$ real, with the
[Michaelis constant](../michaelis-constant.md) $K_M = (k_b + k_2)/k_1$, $\kappa = K_M/s_0$ and
$\sigma = s_0 + K_M$. Let $\bar S : \mathbb{R} \to \mathbb{R}$ be differentiable at every
$\tau \ge 0$ with $\bar S'(\tau) = -k_2 \bar S(\tau)/(K_M + \bar S(\tau))$ there and
$\bar S(0) = s_0$, and put $u(\theta) = \bar S(\sigma\theta/k_2)/s_0$. Let $C_{\mathrm{sub}}(\cdot)$ be the
[constant of the slow-window substrate estimate](../substrate-error-const.md) and define

$$C_c(\delta, T) = \frac{k_2\, s_0}{\exp(1)\,(k_b + k_2)\, \sigma\, \delta} + \frac{\sigma\,(k_1 s_0 + k_b)}{K_M\,(k_b + k_2)} + \frac{\sigma}{K_M}\, C_{\mathrm{sub}}\!\left(\frac{\sigma T}{k_2}\right).$$

Then for every $e_0 > 0$ and every [solution](../is-solution.md) $(s, c, e, p)$ of the
Michaelis–Menten mass-action system with $s(0) = s_0$, $c(0) = 0$ and $e(0) = e_0$, and for every
$\theta \in [\delta, T]$,

$$\left| \frac{c(t_S\, \theta)}{e_0} - h(u(\theta)) \right| \le C_c(\delta, T)\, \varepsilon,$$

where $t_S = \sigma/(k_2 e_0)$ is the [slow time scale](slow-time-scale.md),
$\varepsilon = e_0/\sigma$ the [Segel–Slemrod parameter](qssa-epsilon.md) and
$h(x) = x/(\kappa + x)$ the [slow manifold](slow-manifold.md). For $T < \delta$ the window is empty.
The constant depends on $k_1, k_b, k_2, s_0, \delta$ and $T$ only, and it blows up as $\delta \to 0^+$,
as it must: at $\theta = 0$ the error is $1/(1 + \kappa)$ for every $e_0$
([initial-layer gap](initial-layer-gap.md)).

## Depends on

- [Michaelis constant](../michaelis-constant.md)
- [Constant of the slow-window substrate estimate](../substrate-error-const.md)
- [Solution of the Michaelis–Menten mass-action system](../is-solution.md)
- [Slow time scale of substrate depletion](slow-time-scale.md)
- [Segel–Slemrod small parameter](qssa-epsilon.md)
- [Slow manifold in scaled variables](slow-manifold.md)

## Proof depends on

- [For s₀ > 0, c₀, e₀ ≥ 0, c nears the QSS manifold past an initial layer](../abs-complex-sub-qss-le.md)
- [Standard data: slow-time substrate error at most C ε for 0 ≤ τ ≤ T](../abs-substrate-sub-reduced-le-mul.md)
- [With s₀ > 0 and c₀, e₀ ≥ 0, the substrate stays positive](../substrate-pos.md)
- [A reduced solution that starts positive stays positive](../reduced-pos.md)
- [Quasi-steady-state value of the complex](../qss-complex.md)

## Expansion

Fix $e_0 > 0$, a solution with the standard data, and $\theta \in [\delta, T]$; put $t = t_S\theta$
and $\tau = e_0 t = \sigma\theta/k_2 \in [0, \sigma T/k_2]$. The total enzyme is $e_0$ and the total
substrate $s(0) + c(0)$ is $s_0$. Split the error into three terms.

1. *Slaving with an initial layer.* The real-time complex estimate with $c(0) = 0$ gives
   $|c(t) - q(s(t))| \le q(s_0)\, e^{-(k_b + k_2) t} + e_0^2 (k_1 s_0 + k_b)/(K_M (k_b + k_2))$, with
   $q(x) = e_0 x/(K_M + x)$. Divide by $e_0$ and note $q(s)/e_0 = h(s/s_0)$.
2. *The layer term is $O(\varepsilon)$ for $\theta \ge \delta$.* Here
   $(k_b + k_2) t \ge (k_b + k_2)\sigma\delta/(k_2 e_0) = a/\varepsilon$ with
   $a = (k_b + k_2)\delta/k_2$, and $x e^{-x} \le 1/\exp(1)$ for $x \ge 0$ gives
   $e^{-a/\varepsilon} \le \varepsilon/(\exp(1)\, a)$. With $q(s_0)/e_0 = s_0/\sigma$ this is the first
   summand of $C_c$; the quadratic term divided by $e_0$ is the second summand times $\varepsilon$.
3. *Transfer to the reduced solution.* For $a, b \ge 0$,
   $|h(a) - h(b)| = \kappa |a - b|/((\kappa + a)(\kappa + b)) \le |a - b|/\kappa$. The substrate is
   positive and so is $\bar S$ on $\tau \ge 0$, and the slow-window substrate estimate with
   $\varepsilon$ there equal to $e_0$ gives
   $|s(\tau/e_0)/s_0 - u(\theta)| \le C_{\mathrm{sub}}(\sigma T/k_2)\, e_0/s_0$. Since $1/\kappa = s_0/K_M$ and
   $e_0 = \sigma\varepsilon$, the third summand follows.

The bound has content when $C_c\varepsilon$ is small. The actual normalized error is at most $1$, since $c/e_0$ and $h(u)$ lie in $[0,1]$ along these solutions; the upper bound $C_c\varepsilon$ itself need not be at most $1$ or $2$.

## Sources

- J. Eilertsen, S. Schnell and S. Walcher, "Rigorous estimates for the quasi-steady state approximation
  of the Michaelis–Menten reaction mechanism at low enzyme concentrations", *Nonlinear Analysis: Real World Applications* 78 (2024), 104088, <https://doi.org/10.1016/j.nonrwa.2024.104088>; locators from the version read, arXiv:2305.12602v2 (2024),
  Section 2.1 (the QSS reduction accounts for substrate depletion "after a short transitory phase"),
  Section 2.1, Eq. (8) and Section 5.1, Table 2 (Segel–Slemrod parameter and fast time scale),
  <https://arxiv.org/abs/2305.12602v2>. The explicit complex bound above is derived from the stated complex and substrate estimates; Remark 13(c) concerns substrate error, not complex error.
