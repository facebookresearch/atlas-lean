# The reduced solution on a slow-time window is the rescaled Michaelis–Menten solution

On a slow-time window the reduced problem in the normalized variables has only one solution: the Michaelis–Menten solution with $\bar S(0) = s_0$, divided by $s_0$ and run on the clock $\tau = (s_0 + K_M)\theta/k_2 = e_0 t_S \theta$. It is positive on the window.

Let $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$ and $s_0 > 0$, with the
[Michaelis constant](../michaelis-constant.md) $K_M = (k_b + k_2)/k_1$, the
[dimensionless Michaelis constant](qssa-kappa.md) $\kappa = K_M/s_0$ and $\sigma = s_0 + K_M$. Let
$\bar S : \mathbb{R} \to \mathbb{R}$ be differentiable at every $\tau \ge 0$ with

$$\bar S'(\tau) = -\frac{k_2\, \bar S(\tau)}{K_M + \bar S(\tau)} \quad (\tau \ge 0), \qquad \bar S(0) = s_0 .$$

Let $T$ be real and let $u$ be a [solution of the reduced problem](is-reduced-solution-on.md) on the
slow-time window $[0, T]$: $u(0) = 1$ and $u'(\theta) = F(u(\theta))$ for $\theta \in [0, T]$, with
the [reduced field](reduced-field.md) $F(x) = -(1 + \kappa)\, x/(\kappa + x)$. Then for every
$\theta \in [0, T]$

$$u(\theta) = \frac{1}{s_0}\, \bar S\!\left(\frac{\sigma\, \theta}{k_2}\right) > 0 .$$

Clock identity: for every $e_0 > 0$, the [slow time scale](slow-time-scale.md)
$t_S = \sigma/(k_2 e_0)$ satisfies $e_0\, t_S\, \theta = \sigma \theta/k_2$, so the substrate time
$\tau = e_0 t$ of the Heineken–Tsuchiya–Aris scaling and the slow time $\theta = t/t_S$ of the
Segel–Slemrod scaling are related by $\tau = \sigma\theta/k_2$, and
$u(\theta) = \bar S(e_0\, t_S\, \theta)/s_0$. For $T < 0$ the window is empty and only $u(0) = 1$ is
asserted.

## Depends on

- [Michaelis constant](../michaelis-constant.md)
- [Dimensionless Michaelis constant](qssa-kappa.md)
- [Reduced vector field in slow time](reduced-field.md)
- [Solution of the reduced problem on a slow-time window](is-reduced-solution-on.md)
- [Slow time scale of substrate depletion](slow-time-scale.md)

## Proof depends on

- [A reduced solution that starts positive stays positive](../reduced-pos.md)
- [Reduced vector field in slow time](reduced-field.md)
- [Tube bootstrap for perturbed trajectories](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/tube-bootstrap.md)

## Expansion

Put $w(\theta) = \bar S(\sigma\theta/k_2)/s_0$. By the chain rule, for $\theta \ge 0$,
$w'(\theta) = -(\sigma/s_0)\, w/(\kappa + w) = F(w(\theta))$, since $\sigma/s_0 = 1 + \kappa$, and
$w(0) = 1$. A positive reduced solution stays positive, so $w > 0$ on $[0, \infty)$.

Uniqueness on $[0, T]$ uses that $F$ is smooth, hence locally Lipschitz, on $(-\kappa, \infty)$, which
contains $(0, \infty)$. Let $\theta_1$ be the supremum of the $\theta \in [0, T]$ with $u = w$ on
$[0, \theta]$. By continuity $u(\theta_1) = w(\theta_1) > 0$. If $\theta_1 < T$, both curves stay in
a compact neighbourhood of $w(\theta_1)$ inside $(0, \infty)$ on a short interval
$[\theta_1, \theta_1 + h]$, where $F$ is Lipschitz; the tube bootstrap with perturbation $0$ and
initial distance $0$ gives $u = w$ there, contradicting maximality. Hence $u = w$ on $[0, T]$.

The convention that $F$ reads $0$ at $x = -\kappa$ never matters, because the solution stays positive.

## Sources

- G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
  Mathematics 140, American Mathematical Society (2012), Theorem 2.2 (Picard–Lindelöf) and the
  opening uniqueness argument of Section 2.6, pp. 38 and 50–51 in the
  [author's preliminary version](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf).
  This is the uniqueness theorem applied to $F$ on $(-\kappa,\infty)$ after the linear change
  of state and time. [Positivity of the supplied reduced solution](../reduced-pos.md) keeps
  the rescaled curve inside that open domain; the continuation argument above proves equality
  without assuming in advance that the other window solution stays in the domain.
- Model and scaling background: J. Eilertsen, S. Schnell and S. Walcher, "Rigorous estimates for the quasi-steady state approximation
  of the Michaelis–Menten reaction mechanism at low enzyme concentrations", *Nonlinear Analysis: Real World Applications* 78 (2024), 104088, <https://doi.org/10.1016/j.nonrwa.2024.104088>; locators from the version read, arXiv:2305.12602v2 (2024),
  Section 1, Eq. (2) (the Michaelis–Menten reduction $\dot s = -k_1 k_2 e_0 s/(k_{-1} + k_2 + k_1 s)$),
  Section 2.1, Eq. (8) (Segel–Slemrod parameter $e_0/(K_M + s_0)$) and Section 5.1, Table 2,
  <https://arxiv.org/abs/2305.12602v2>.
