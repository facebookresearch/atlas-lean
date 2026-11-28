# Rescaling a positive reduced trajectory solves the normalized equation

Dividing a supplied positive Michaelis–Menten trajectory by its initial concentration and changing its clock gives a solution of the normalized reduced initial-value problem on every slow-time window. This is a forward change of variables, not an identification of arbitrary window solutions.

Let $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$ and $s_0 > 0$, with the
[Michaelis constant](../michaelis-constant.md) $K_M = (k_b + k_2)/k_1$, the
[dimensionless Michaelis constant](qssa-kappa.md) $\kappa = K_M/s_0$ and $\sigma = s_0 + K_M$.
Suppose $\bar S : \mathbb{R} \to \mathbb{R}$ satisfies $\bar S(\tau)>0$ for every $\tau\ge0$
and has a two-sided derivative at every such $\tau$, with

$$\bar S'(\tau) = -\frac{k_2\,\bar S(\tau)}{K_M + \bar S(\tau)} \quad (\tau \ge 0), \qquad \bar S(0) = s_0 .$$

Define $w : \mathbb{R} \to \mathbb{R}$ by

$$w(\theta) = \frac{1}{s_0}\,\bar S\!\left(\frac{\sigma\,\theta}{k_2}\right).$$

Then $w(0) = 1$ and, for every $\theta \ge 0$, $w(\theta) > 0$ and $w$ has the two-sided derivative

$$w'(\theta) = -\frac{(1 + \kappa)\,w(\theta)}{\kappa + w(\theta)} = F(w(\theta)),$$

where $F$ is the [reduced field](reduced-field.md). Consequently, for every real $T$, this defined
$w$ is a [solution of the reduced problem](is-reduced-solution-on.md) on $[0,T]$. For $T < 0$ that
window condition requires only $w(0) = 1$.

For any $e_0 > 0$, the [slow time scale](slow-time-scale.md) $t_S = \sigma/(k_2 e_0)$ satisfies
$e_0 t_S\theta = \sigma\theta/k_2$. Thus the same definition reads
$w(\theta) = \bar S(e_0 t_S\theta)/s_0$ when $\tau = e_0t$ and $\theta = t/t_S$.
This statement neither constructs $\bar S$ nor asserts uniqueness of independently supplied window solutions.

## Depends on

- [Michaelis constant](../michaelis-constant.md)
- [Dimensionless Michaelis constant](qssa-kappa.md)
- [Reduced vector field in slow time](reduced-field.md)
- [Solution of the reduced problem on a slow-time window](is-reduced-solution-on.md)
- [Slow time scale of substrate depletion](slow-time-scale.md)

## Proof depends on

- [Chain rule for derivatives of functions of one variable over normed fields](../../../../Analysis/calculus-in-normed-spaces/frechet-derivatives/chain-rule-holomorphic.md)

## Expansion

For $\theta \ge 0$, put $\tau = \sigma\theta/k_2 \ge 0$. The chain rule, first for the linear clock
and then for division by $s_0$, gives

$$w'(\theta) = \frac{\sigma}{k_2s_0}\,\bar S'(\tau)
= -\frac{\sigma}{s_0}\,\frac{\bar S(\tau)}{K_M + \bar S(\tau)}
= -\frac{(1+\kappa)\,w(\theta)}{\kappa+w(\theta)}.$$

Here $K_M + \bar S(\tau) = s_0(\kappa + w(\theta)) > 0$ and $\sigma/s_0 = 1+\kappa$.
The initial value follows from $\bar S(0)/s_0 = 1$, and positivity is inherited from the supplied
$\bar S$. Restricting this derivative identity to $[0,T]$ gives the stated window predicate.
No uniqueness or continuation argument is used.

## Sources

- The forward derivative calculation specializes the
  [one-variable chain rule](../../../../Analysis/calculus-in-normed-spaces/frechet-derivatives/chain-rule-holomorphic.md),
  `HasDerivAt.comp` over $\mathbb{R}$, to the two linear maps displayed above and the supplied trajectory.
  The normalization is the explicit algebra in the expansion, not an ODE uniqueness theorem.
- J. Eilertsen, S. Schnell and S. Walcher, "Rigorous estimates for the quasi-steady state approximation
  of the Michaelis–Menten reaction mechanism at low enzyme concentrations", *Nonlinear Analysis: Real World Applications* 78 (2024), 104088,
  <https://doi.org/10.1016/j.nonrwa.2024.104088>; version read: arXiv:2305.12602v2 (2024),
  Section 1, Eqs. (2)–(4) and footnote 1, <https://arxiv.org/abs/2305.12602v2>.
  These give the dimensional reduced equation $ds/dt=-k_2e_0s/(K_M+s)$ and the usual initial value
  $s(0)=s_0$. Writing $\tau=e_0t$ gives the assumed equation for $\bar S$; the displayed state/time
  change gives its normalized form. No approximation error bound is asserted.
