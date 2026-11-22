# First-order convergence of the explicit Euler method

Let $E$ be a real Banach space,
let $t_0 < T$, let $x_0 \in E$ and $L \ge 0$, and let $f : \mathbb{R} \times E \to E$ be $C^2$
with $f(t, \cdot)$ $L$-Lipschitz for every $t \in [t_0, T]$. Then there are a function
$x : \mathbb{R} \to E$ with $x(t_0) = x_0$ and $x'(t) = f(t, x(t))$ for every $t \in [t_0, T]$,
and a constant $C$, such that the following holds for every step size $h \in (0, T - t_0]$: if
$(X_n)_{n \in \mathbb{N}}$ is the explicit Euler sequence $X_0 = x_0$,
$X_{n+1} = X_n + h f(t_0 + n h, X_n)$, then $\|X_n - x(t_0 + n h)\| \le C h$ for every
$n \in \mathbb{N}$ with $n h \le T - t_0$.

Proof: clamp the time variable and use global existence for globally Lipschitz right-hand
sides. The local truncation bound and the discrete Grönwall inequality then give the
first-order global estimate.

## Sources

- E. Hairer, S. P. Nørsett and G. Wanner, Solving Ordinary Differential Equations I, 2nd ed., Theorem I.7.3; stable ref https://en.wikipedia.org/wiki/Euler_method.
