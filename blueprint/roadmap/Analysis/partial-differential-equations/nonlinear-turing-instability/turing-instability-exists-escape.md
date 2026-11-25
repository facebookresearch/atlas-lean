# Nonlinear Turing instability, time-map form

Let $X = C([0, L], \mathbb{R}^2)$ with the sup norm (and the sup norm $\max(|w_0|, |w_1|)$ on
$\mathbb{R}^2$). A C₀ semigroup on $X$ is a family $(P(t))_{t \ge 0}$ of bounded linear operators
with $P(0)$ the identity, $P(s + t) = P(s) P(t)$, continuous orbits $t \mapsto P(t) x$, and
$\lVert P(t) \rVert$ bounded on bounded time intervals. Let $J$ be a real $2 \times 2$ matrix with
$\operatorname{tr} J < 0$ and $\det J > 0$ (kinetics stable without diffusion), let $d_u, d_v \ge 0$
and $L \ge 0$, let $n \in \mathbb{N}$, and suppose the mode with the
[Neumann wavenumber](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/neumann-wavenumber.md)
$k_n = n\pi/L$ is
[linearly unstable](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md):
the mode matrix $J - k_n^2 D$, with $D = \operatorname{diag}(d_u, d_v)$, has a complex eigenvalue
with positive real part. Let $\lambda$ be the [growth rate](growth-rate.md) of the mode $k_n$,
positive under these hypotheses. Let $u_0 \in X$, let $\Phi : \mathbb{R} \times X \to X$, and let
$T > 0$, $\rho > 0$, $C \ge 0$, $p > 1$ and $M, \omega$ be real. Assume:

- **semigroup:** $S$ is a C₀ semigroup on $X$, it acts on the Neumann mode $n$ through the ODE
  $c' = (J - k_n^2 D)\, c$: for every $w \in \mathbb{R}^2$,
  $S(t)(\cos(k_n \cdot)\, w) = \cos(k_n \cdot)\, c(t)$ for $t \ge 0$, where $c(0) = w$
  ([modal action](acts-by-modal-ode.md)), it acts on the Neumann mode $0$ (the constant fields)
  through the kinetics ODE $c' = J c$, and $\lVert S(t) \rVert \le M e^{\omega t}$ for every
  $t \ge 0$, with $\omega < p\lambda$;
- **flow:** $\Phi(0, x) = x$ for every $x$, and for every $m \in \mathbb{N}$ and $x \in X$ with
  $\lVert \Phi(kT, x) - u_0 \rVert \le \rho$ for $k = 0, \dots, m$,
  $\Phi((m + 1)T, x) = \Phi(T, \Phi(mT, x))$;
- **time-$T$ map:** $\lVert \Phi(T, u_0 + y) - u_0 - S(T)\, y \rVert \le C \lVert y \rVert^p$
  whenever $\lVert y \rVert \le \rho$.

Then:

- homogeneous perturbations stay bounded under $S$: there is $C'$ with
  $\lVert S(t)\, w \rVert \le C' \lVert w \rVert$ for every constant field $w \in \mathbb{R}^2$ and
  $t \ge 0$;
- the homogeneous mode $k = 0$ is not linearly unstable;
- the unstable mode is not homogeneous: $n \ge 1$;
- $u_0$ is nonlinearly unstable for $\Phi$: there is $\varepsilon > 0$ such that for every
  $\delta_0 > 0$ there are $x \in X$ with $\lVert x - u_0 \rVert < \delta_0$ and a time $t \ge 0$
  with $\lVert \Phi(t, x) - u_0 \rVert \ge \varepsilon$.

In applications $u_0$ is the homogeneous steady state with kinetics Jacobian $J$, $S$ the linearized
semigroup and $\Phi$ the reaction–diffusion flow: a steady state that is stable for the kinetics
alone is destabilised by diffusion.
