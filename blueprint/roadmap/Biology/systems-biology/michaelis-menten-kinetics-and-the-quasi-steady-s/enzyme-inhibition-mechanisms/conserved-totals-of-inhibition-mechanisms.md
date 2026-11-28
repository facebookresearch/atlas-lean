# Conserved totals of the inhibition mechanisms

Along every solution of the mixed-inhibition mass-action system, total enzyme, total inhibitor and total substrate moiety stay constant. The free inhibitor is the total minus the bound inhibitor, so it equals the total only when no inhibitor is bound.

For all real rate constants, let $(s, i, e, c, y, z, p)$ solve the
[mixed-inhibition mechanism](mixed-inhibition-mechanism.md) on $[0, \infty)$. Then for every
$t \ge 0$

$$e(t) + c(t) + y(t) + z(t) = e_T, \qquad i(t) + y(t) + z(t) = i_T, \qquad s(t) + c(t) + z(t) + p(t) = s_T,$$

where $e_T$, $i_T$ and $s_T$ are the same sums at $t = 0$. The same holds for the
[competitive mechanism](competitive-inhibition-mechanism.md) with $z$ deleted:
$e + c + y = e_T$, $i + y = i_T$, $s + c + p = s_T$.

Consequently, at any $t \ge 0$ with $y(t), z(t) \ge 0$, the free inhibitor satisfies
$0 \le i_T - i(t) = y(t) + z(t)$, with $i(t) = i_T$ exactly when $y(t) + z(t) = 0$; and when also
$c(t) \ge 0$, $y(t) + z(t) \le e_T - e(t)$. So replacing free by total inhibitor is an
approximation whose error is the bound inhibitor, at most the bound enzyme.

## Depends on

- [Mixed-inhibition mechanism](mixed-inhibition-mechanism.md)
- [Competitive-inhibition mechanism](competitive-inhibition-mechanism.md)

## Proof depends on

- [Mixed-inhibition mechanism](mixed-inhibition-mechanism.md)
- [Competitive-inhibition mechanism](competitive-inhibition-mechanism.md)
- [Left-null weighted totals have zero derivative under the rate law](../../../../Chemistry/chemical-kinetics/conservation-laws-of-reaction-networks/stoichiometric-left-null-conserved.md)
- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

In the species order $(S, I, E, ES, EI, ESI, P)$ the three weight vectors
$(0, 0, 1, 1, 1, 1, 0)$, $(0, 1, 0, 0, 1, 1, 0)$ and $(1, 0, 0, 1, 0, 1, 1)$ are orthogonal to every
reaction vector $\mathrm{prod}(r) - \mathrm{src}(r)$ (check the seven reactions one by one). The
mass-action field is the stoichiometric matrix applied to the mass-action rates, so each weighted total
has derivative zero at every $t \ge 0$; a function with zero derivative on $[0, \infty)$ is constant
there. The inequalities follow by subtraction. Nonnegativity of the complexes is a hypothesis here,
not derived.

## Sources

- J. Eilertsen, S. Schnell and S. Walcher, "Natural parameter conditions for singular perturbations of
  chemical and biochemical reaction networks", *Bulletin of Mathematical Biology* 85 (2023), article 48, <https://doi.org/10.1007/s11538-023-01150-7>; locators from the version read, arXiv:2211.10836v2 (2023), Section 6.3, Eq. (75)
  (competitive mechanism written, with mass-action kinetics and the stoichiometric conservation laws,
  in terms of free enzyme $e_0 - c_1 - c_2$ and free inhibitor $i_0 - c_2$) and Section 6.2, Eq. (65)
  (uncompetitive mechanism with free enzyme $e_0 - c_1 - c_2$ and free inhibitor $i_0 - c_2$),
  <https://arxiv.org/abs/2211.10836v2>.
