# Kamke comparison bounds for Michaelis–Menten kinetics at low substrate

**Setting.** With total enzyme $e_0 > 0$, rate constants $k_1, k_{-1}, k_2 > 0$ and initial substrate
$s_0 > 0$, the reduced Michaelis–Menten system for substrate $s$ and complex $c$ is

$$\dot s = -k_1 e_0 s + (k_1 s + k_{-1}) c, \qquad \dot c = k_1 e_0 s - (k_1 s + k_{-1} + k_2) c,$$

with $s(0) = s_0$, $c(0) = 0$. Write $K_S = k_{-1}/k_1$, $K_M = (k_{-1}+k_2)/k_1$ and the
van Slyke–Cullen constant $K = k_2/k_1 = K_M - K_S$. Its linearization at the origin, the **linear
(pseudo-first-order) Michaelis–Menten system**, is

$$\begin{pmatrix}\dot s\\ \dot c\end{pmatrix} = k_1 \begin{pmatrix} -e_0 & K_S \\ e_0 & -K_M \end{pmatrix}\begin{pmatrix} s\\ c\end{pmatrix}.$$

**Statement.** On $D = \{(s,c) : s \ge 0,\ 0 \le c \le e_0,\ s + c \le s_0\}$, which is convex and
positively invariant, the Michaelis–Menten system is cooperative (its Jacobian has nonnegative
off-diagonal entries $k_1 s + k_{-1}$ and $k_1(e_0 - c)$). By Kamke's comparison theorem, the solution
$(s, c)$ is bounded componentwise for all $t \ge 0$ by the solutions of two linear systems with the same
initial value:

$$G = k_1\begin{pmatrix} -e_0 & K_S \\ e_0 & -(K_M + s_0)\end{pmatrix} \ \text{(lower bound)}, \qquad
H = k_1\begin{pmatrix} -e_0 & K_S + s_0 \\ e_0 & -K_M\end{pmatrix} \ \text{(upper bound)}.$$

For any matrix $\begin{pmatrix} -\alpha & \beta \\ \alpha & -\gamma\end{pmatrix}$ with positive entries
and $\gamma > \beta$, the solution from $(s_0, 0)$ is

$$\begin{pmatrix}\tilde s\\ \tilde c\end{pmatrix} = \frac{s_0}{2\sqrt{\Delta}}\left[\begin{pmatrix} \gamma - \alpha + \sqrt{\Delta} \\ 2\alpha\end{pmatrix} e^{\frac12(-\alpha-\gamma+\sqrt{\Delta})t} + \begin{pmatrix} \alpha - \gamma + \sqrt{\Delta} \\ -2\alpha\end{pmatrix} e^{\frac12(-\alpha-\gamma-\sqrt{\Delta})t}\right],$$

with $\Delta = (\alpha - \gamma)^2 + 4\alpha\beta$. Taking $(\alpha,\beta,\gamma) = (k_1 e_0, k_1 K_S, k_1 K_M)$
gives the linear solution $(s^*, c^*)$; replacing $K_M$ by $K_M + s_0$ gives the lower bound
$(s_{\mathrm{low}}, c_{\mathrm{low}})$, and replacing $K_S$ by $K_S + s_0$ gives the upper bound
$(s_{\mathrm{up}}, c_{\mathrm{up}})$. If $s_0 < K$, then for all $t \ge 0$

$$s_{\mathrm{low}} \le s,\, s^* \le s_{\mathrm{up}}, \qquad c_{\mathrm{low}} \le c,\, c^* \le c_{\mathrm{up}}.$$

When $s_0 > K$ one eigenvalue of $H$ is positive and the upper bound is useless, so $s_0 < K$ is the
natural regime for the two-sided estimate.

## Depends on

- [Solution of the Michaelis–Menten mass-action system](../../michaelis-menten-kinetics-and-the-quasi-steady-s/is-solution.md)
- [Michaelis constant](../../michaelis-menten-kinetics-and-the-quasi-steady-s/michaelis-constant.md)

## Expansion

Kamke's theorem says that if $\dot x = f(x)$ is cooperative on a convex positively invariant set and
$f \prec g$ there (componentwise), then solutions are ordered: $x(0) \prec y(0)$ implies
$x(t) \prec y(t)$ for $t \ge 0$. On $D$ the bounds $0 \le s \le s_0$ and $0 \le c$ give
$-k_1 s c \ge -k_1 s_0 c$ and $k_1 s c \le k_1 s_0 c$, which are exactly the inequalities
$Gx \preceq f(x) \preceq Hx$ for the two right-hand sides. Both comparison matrices tend to the
linearization as $s_0 \to 0$, which is what makes the bounds tight at low substrate. The trace of the
generic matrix is $-(\alpha+\gamma)$ and its determinant is $\alpha(\gamma - \beta)$; for $H$ the
determinant $k_1^2 e_0 (K - s_0)$ changes sign at $s_0 = K$.

## Sources

- J. Eilertsen, S. Schnell, S. Walcher, "The Michaelis–Menten reaction at low substrate concentrations: pseudo-first-order kinetics and conditions for timescale separation", Bulletin of Mathematical Biology (2024), <https://doi.org/10.1007/s11538-024-01295-z> (PMC11069484). Proposition 1 (Kamke comparison), Lemma 1, Remark 1, Lemma 2 and Proposition 2(a)–(d), Eqs. (1), (2), (4), (6)–(8).
