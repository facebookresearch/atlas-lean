# Asymptotic speed of propagation for the spatial Kermack–McKendrick epidemic

Diekmann (1979) studies the nonlinear integral equation

$$u(t, x) = \int_0^t A(t - \tau)\int_{\mathbb{R}^n} g(u(\tau, \xi))\,V(x - \xi)\,d\xi\,d\tau + f(t, x), \qquad t \ge 0,\ x \in \mathbb{R}^n,$$

which models the spatio-temporal spread of an epidemic (Eq. (1.1)), under hypotheses on the data: $A \ge 0$ and $V \ge 0$ are integrable with integral $1$, $V$ is radial and satisfies the exponential-moment hypothesis $H_V$ of Section 2 (a condition on exponential moments of $V$, not a pointwise bound on its tails), $g$ is continuously differentiable with $g(0) = 0$, $g'(0) > 1$, $0 < g' < C$, and $g(x) > x$ for $0 < x < p$ and $g(p) = p$ for some $p > 0$ (hypothesis $H_g$, so that $p$ is the least positive fixed point of $g$), and $f$ is nonnegative but not identically zero with $f \in C(\mathbb{R}_+; BC(\mathbb{R}^n))$ (hypothesis $H_f$); the solution $u$ is taken in $C(\mathbb{R}_+; BC(\mathbb{R}^n))$ (Section 2). From the characteristic equation of the linearized wave equation the source defines a minimal wave speed $c_0 \in (0, \infty)$ (Eq. (2.8)) and recalls from earlier work of Diekmann and of Diekmann and Kaper that, under extra technical assumptions concerning $A$, $V$ and $g$, travelling waves of speed $c$ exist for $c \ge c_0$ and do not exist for $0 \le c < c_0$. It proves that $c_0$ is the asymptotic speed of propagation: if $f$ is bounded with uniformly compact support in $x$ and $g(x) \le g'(0)x$, then $\sup\{u(t, x) : |x| \ge ct\} \to 0$ for every $c > c_0$ (Theorem 1); and for every $c \in (0, c_0)$, $\liminf_{t \to \infty}\min\{u(t, x) : |x| \le ct\} \ge p$ (Theorem 2).

## Expansion

1. The model: the integral equation (1.1), its derivation from the spatial Kermack–McKendrick model (Section 5 of the source), and hypotheses on $A$, $V$, $g$, $f$.
2. The travelling-wave equation (2.1)–(2.2), the characteristic function and the definition of $c_0$.
3. Existence of travelling waves for $c \ge c_0$ and their nonexistence for $c < c_0$, as recalled from the earlier papers under their extra technical assumptions on $A$, $V$ and $g$.
4. Theorem 1 by comparison with the linearized equation, and Theorem 2 by subsolutions built after Aronson and Weinberger.
5. Comparison with the [Fisher–KPP travelling waves](../../../Biology/pattern-formation/fisher-kpp-travelling-waves/has-deriv-at-wave-xx.md) as the reaction–diffusion analogue.

## Sources

- O. Diekmann, Run for your life. A note on the asymptotic speed of propagation of an epidemic, J. Differential Equations 33 (1979), 58–73, Section 2 and Theorems 1 and 2. <https://doi.org/10.1016/0022-0396(79)90080-9>
- Original result: O. Diekmann, Thresholds and travelling waves for the geographical spread of infection, J. Math. Biol. 6 (1978), 109–130. <https://doi.org/10.1007/bf02450783> The existence and nonexistence of travelling waves follow Diekmann (1979), Section 2.
