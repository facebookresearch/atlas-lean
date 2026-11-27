# Nonlinear Turing instability, mild formulation

Let $X = C([0, L], \mathbb{R}^2)$ with the sup norm (and the sup norm $\max(|w_0|, |w_1|)$ on
$\mathbb{R}^2$). A C₀ semigroup on $X$ is a family $(P(t))_{t \ge 0}$ of bounded linear operators
with $P(0)$ the identity, $P(s + t) = P(s) P(t)$, continuous orbits $t \mapsto P(t) x$, and
$\lVert P(t) \rVert$ bounded on bounded time intervals. Consider the two-species system
$u_t = D u_{xx} + f(u)$ on $[0, L]$ with Neumann boundary conditions,
$D = \operatorname{diag}(d_u, d_v)$, at a homogeneous steady state $a \in \mathbb{R}^2$ (identified
with the constant field), with $J$ a real $2 \times 2$ matrix, $n \in \mathbb{N}$, a time $T > 0$,
real $M, \omega, R$ and a map $\Phi : \mathbb{R} \times X \to X$. For a C₀ semigroup $S_A$ on $X$
and $G : X \to X$, a mild solution of $w' = A w + G(w)$ on $[0, T]$ from $w_0$ is a curve $w$
continuous on $[0, T]$ with integrable integrands $s \mapsto S_A(t - s)\, G(w(s))$ on $[0, t]$ and
$w(t) = S_A(t)\, w_0 + \int_0^t S_A(t - s)\, G(w(s))\, ds$ for every $t \in [0, T]$, where $A$ is
the generator of $S_A$. Assume $\det J > 0$ (with $\operatorname{tr} J < 0$ below, the kinetics are
stable without diffusion) and:

- **spectral input:** $\operatorname{tr} J < 0$, $d_u, d_v \ge 0$, $L \ge 0$, and the mode with the
  [Neumann wavenumber](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/neumann-wavenumber.md)
  $k_n = n\pi/L$ is
  [linearly unstable](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md):
  the mode matrix $J - k_n^2 D$, with $D = \operatorname{diag}(d_u, d_v)$, has a complex eigenvalue
  with positive real part;
- **kinetics:** $f : \mathbb{R}^2 \to \mathbb{R}^2$ is continuous and Lipschitz on every closed ball
  centred at $0$, $f(a) = 0$, and for some $r > 0$, $K \ge 0$ and $p > 1$,
  $\lVert f(a + z) - f(a) - J z \rVert \le K \lVert z \rVert^p$ whenever $\lVert z \rVert \le r$
  (for example $f$ of class $C^2$ with $p = 2$);
- **semigroups:** $S_A$ is a C₀ semigroup on $X$ that fixes the constant field $a$; $S$ is a C₀
  semigroup on $X$ whose orbits $t \mapsto S(t)\, y$ are mild solutions of the linearized equation
  $w' = A w + J w$ on $[0, T]$ (with $J w$ the [pointwise action](pointwise-matrix.md)); $S$ acts on
  the Neumann mode $n$ through the ODE $c' = (J - k_n^2 D)\, c$: for every $w \in \mathbb{R}^2$,
  $S(t)(\cos(k_n \cdot)\, w) = \cos(k_n \cdot)\, c(t)$ for $t \ge 0$, where $c(0) = w$
  ([modal action](acts-by-modal-ode.md)); $S$ also acts on the Neumann mode $0$ (the constant
  fields) through the kinetics ODE $c' = J c$; and $\lVert S(t) \rVert \le M e^{\omega t}$ for every
  $t \ge 0$, with $\omega < p\lambda$ for the [growth rate](growth-rate.md) $\lambda$ of the mode
  $k_n$;
- **flow:** $\rho_0 > 0$; $\Phi(0, x) = x$ for every $x$; for every $m \in \mathbb{N}$ and $x$ with
  $\lVert \Phi(kT, x) - a \rVert \le \rho_0$ for $k = 0, \dots, m$,
  $\Phi((m + 1)T, x) = \Phi(T, \Phi(mT, x))$; and for every $x$ with
  $\lVert x - a \rVert \le \rho_0$, $t \mapsto \Phi(t, x)$ is a mild solution of $w' = A w + F(w)$,
  $F(w) = f \circ w$, on $[0, T]$ from $x$, with $\lVert \Phi(t, x) \rVert \le R$ for
  $t \in [0, T]$.

Then:

- homogeneous perturbations stay bounded under $S$: there is $C'$ with
  $\lVert S(t)\, w \rVert \le C' \lVert w \rVert$ for every constant field $w \in \mathbb{R}^2$ and
  $t \ge 0$;
- the homogeneous mode $k = 0$ is not linearly unstable;
- the unstable mode is not homogeneous: $n \ge 1$;
- the steady state is nonlinearly unstable for $\Phi$: there is $\varepsilon > 0$ such that for
  every $\delta_0 > 0$ there are $x \in X$ with $\lVert x - a \rVert < \delta_0$ and a time
  $t \ge 0$ with $\lVert \Phi(t, x) - a \rVert \ge \varepsilon$.
