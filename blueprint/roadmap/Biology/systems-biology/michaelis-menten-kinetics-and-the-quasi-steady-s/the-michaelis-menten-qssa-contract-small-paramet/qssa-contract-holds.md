# The Michaelis–Menten QSSA contract holds

For all rate constants, initial substrates and window lengths, the Michaelis–Menten QSSA contract is true: on a compact slow-time window, every window solution with standard data has normalized substrate error at most $C\varepsilon$ on $[0, T]$ and normalized complex error at most $C\varepsilon$ on $[\delta, T]$, with $C$ independent of $e_0$.

For all real $k_1, k_b, k_2, s_0$ and $T$, the proposition
[QSSA contract for the Michaelis–Menten system](qssacontract.md) holds. Unfolded: let $k_1 > 0$,
$k_b \ge 0$, $k_2 > 0$ and $s_0 > 0$, write $K_M = (k_b + k_2)/k_1$, $\kappa = K_M/s_0$,
$\sigma = s_0 + K_M$, and for $e_0 > 0$ let $t_S = \sigma/(k_2 e_0)$ and
$\varepsilon = e_0/\sigma$. Let $u$ be a
[solution of the reduced problem](is-reduced-solution-on.md) on $[0, T]$ and let
$\delta \in (0, T]$. Put

$$C = \frac{\sigma}{s_0}\, C_{\mathrm{sub}}\!\left(\frac{\sigma T}{k_2}\right) + C_c(\delta, T),$$

with $C_{\mathrm{sub}}(\cdot)$ the [constant of the slow-window substrate estimate](../substrate-error-const.md)
and $C_c(\delta, T)$ the constant of the
[normalized complex estimate](normalized-complex-error-past-the-initial-layer.md). Then for every
$e_0 > 0$ and every pair $(s, c)$ that
[solves the system on the window](is-solution-on.md) $[0, t_S T]$ with total enzyme $e_0$,
$s(0) = s_0$ and $c(0) = 0$:

- $|s(t_S\theta)/s_0 - u(\theta)| \le C\varepsilon$ for every $\theta \in [0, T]$, and
- $|c(t_S\theta)/e_0 - u(\theta)/(\kappa + u(\theta))| \le C\varepsilon$ for every
  $\theta \in [\delta, T]$.

The constant depends on $k_1, k_b, k_2, s_0, T$ and $\delta$ only. This page asserts the contract;
the contract page itself only defines the proposition. The excluded initial layer cannot be
removed: for $C\varepsilon < 1/(1 + \kappa)$ the complex bound
[fails at θ = 0](not-complex-le-at-zero.md). The hypotheses are
[satisfiable](qssa-contract-hypotheses-are-satisfiable.md) for every $T$ and $e_0 > 0$, so the
statement is not vacuous for $T > 0$.

## Depends on

- [QSSA contract for the Michaelis–Menten system](qssacontract.md)
- [Solution of the reduced problem on a slow-time window](is-reduced-solution-on.md)
- [Solution of the Michaelis–Menten system on a time window](is-solution-on.md)
- [Constant of the slow-window substrate estimate](../substrate-error-const.md)
- [Normalized complex error past the initial layer](normalized-complex-error-past-the-initial-layer.md)

## Proof depends on

- [Window solutions of the Michaelis–Menten system are unique](window-solution-uniqueness.md)
- [The reduced solution on a slow-time window is the rescaled Michaelis–Menten solution](reduced-solution-on-window-is-rescaled.md)
- [Normalized complex error past the initial layer](normalized-complex-error-past-the-initial-layer.md)
- [Standard data: slow-time substrate error at most C ε for 0 ≤ τ ≤ T](../abs-substrate-sub-reduced-le-mul.md)
- [For K > 0 a positive reduced solution passes through every s₀ > 0](../exists-reduced-solution.md)
- [Global nonnegative trajectories exist from nonnegative data](../global-positive-trajectories-of-the-michaelis-me/exists-is-solution-nonneg.md)
- [A global solution solves the system on every window](is-solution-on-2.md)
- [Constant of the slow-window substrate estimate](../substrate-error-const.md)

## Expansion

Outside the parameter premises the contract is vacuous, and for $T \le 0$ there is no $\delta$; so
assume the premises and $0 < \delta \le T$.

1. *Reduced solution.* Take a positive global solution $\bar S$ of
   $\bar S' = -k_2\bar S/(K_M + \bar S)$ with $\bar S(0) = s_0$. By the rescaling lemma,
   $u(\theta) = \bar S(\sigma\theta/k_2)/s_0$ on $[0, T]$; the given $u$ plays no other role, which is
   why $C$ does not depend on it.
2. *Window solution.* Fix $e_0 > 0$ and a window solution $(s, c)$ on $[0, t_S T]$ with standard
   data. Take the global nonnegative solution $(\hat s, \hat c, \hat e, \hat p)$ with data
   $(s_0, 0, e_0, 0)$; it is a window solution with total enzyme $e_0$, so window uniqueness gives
   $s = \hat s$ and $c = \hat c$ on $[0, t_S T]$, since $t_S T \ge 0$.
3. *Substrate clause.* With $\tau = \sigma\theta/k_2 = e_0 t_S \theta \in [0, \sigma T/k_2]$, the
   slow-window substrate estimate (its parameter is $e_0$) gives
   $|\hat s(\tau/e_0) - \bar S(\tau)| \le C_{\mathrm{sub}}(\sigma T/k_2)\, e_0$; divide by $s_0$ and use
   $e_0 = \sigma\varepsilon$.
4. *Complex clause.* The normalized complex estimate applied to the global solution gives the bound
   $C_c(\delta, T)\varepsilon$ on $[\delta, T]$.

Both bounds are at most $C\varepsilon$. The clock identity $t_S\theta = \tau/e_0$ is the only link
between the Heineken–Tsuchiya–Aris time $\tau = e_0 t$ of the global estimates and the slow time
$\theta$ of the contract.

## Sources

- J. Eilertsen, S. Schnell and S. Walcher, "Rigorous estimates for the quasi-steady state approximation
  of the Michaelis–Menten reaction mechanism at low enzyme concentrations", *Nonlinear Analysis: Real World Applications* 78 (2024), 104088, <https://doi.org/10.1016/j.nonrwa.2024.104088>; locators from the version read, arXiv:2305.12602v2 (2024),
  Section 2.1 (standard QSS reduction, Tikhonov's theorem as applied by Heineken, Tsuchiya and Aris;
  Eqs. (6) and (8)), Section 3.3, Remark 13(c) and Section 5.1, Table 2,
  <https://arxiv.org/abs/2305.12602v2>.
