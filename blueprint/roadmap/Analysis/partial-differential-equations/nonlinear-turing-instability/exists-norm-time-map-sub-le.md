# Time-T map expansion from a Hölder-differentiable reaction

Let $X$ be a real Banach space and $S_A$ a C₀ semigroup on $X$ (a family $(S_A(t))_{t \ge 0}$ of
bounded linear operators with $S_A(0)$ the identity, $S_A(s + t) = S_A(s) S_A(t)$, continuous
orbits, and $\lVert S_A(t) \rVert$ bounded on bounded time intervals), with generator $A$. For
$G : X \to X$, call $w : \mathbb{R} \to X$ a mild solution of $w' = A w + G(w)$ on $[0, T]$ from
$w_0$ when $w$ is continuous on $[0, T]$, the integrands $s \mapsto S_A(t - s)\, G(w(s))$ are
integrable on $[0, t]$ and $w(t) = S_A(t)\, w_0 + \int_0^t S_A(t - s)\, G(w(s))\, ds$ for every
$t \in [0, T]$.

Let $F : X \to X$ be Lipschitz on every closed ball $\{\lVert x \rVert \le R'\}$, let $B$ be a
bounded linear operator on $X$, and let $T \ge 0$, $\rho_0 > 0$, $r > 0$, $K \ge 0$, $p \ge 0$ and
$R$ be real. Assume:

- **equilibrium:** $u_0 \in X$ satisfies $S_A(t)\, u_0 = u_0$ for every $t \ge 0$ and $F(u_0) = 0$;
- **Hölder remainder:** $\lVert F(u_0 + z) - F(u_0) - B z \rVert \le K \lVert z \rVert^p$ whenever
  $\lVert z \rVert \le r$;
- **linearized semigroup:** $S = (S(t))_{t \ge 0}$ is a family of bounded linear operators such
  that, for every $y$, $t \mapsto S(t)\, y$ is a mild solution of $w' = A w + B w$ on $[0, T]$ from
  $y$;
- **flow:** for every $x$ with $\lVert x - u_0 \rVert \le \rho_0$, $t \mapsto \Phi(t, x)$ is a mild
  solution of $w' = A w + F(w)$ on $[0, T]$ from $x$, with $\lVert \Phi(t, x) \rVert \le R$ for
  $t \in [0, T]$.

Then there are $\rho > 0$ and $C \ge 0$ such that for every $y$ with $\lVert y \rVert \le \rho$

$$\lVert \Phi(T, u_0 + y) - u_0 - S(T)\, y \rVert \le C \lVert y \rVert^p.$$

The powers are real powers, with $0^0 = 1$. The proof writes the error as a Duhamel integral, bounds
the distance of the orbit from $u_0$ by Lipschitz dependence on initial data, and closes with
Grönwall's inequality.
