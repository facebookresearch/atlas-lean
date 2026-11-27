# Pseudo-first-order approximation of Michaelis–Menten kinetics at low substrate

**Setting.** The irreversible mechanism $S + E \rightleftarrows C \to P + E$ with rate constants $k_1, k_{-1}, k_2$, total enzyme $e_0$ and initial data $(s, c)(0) = (s_0, 0)$ gives $\dot s = -k_1 e_0 s + (k_1 s + k_{-1}) c$, $\dot c = k_1 e_0 s - (k_1 s + k_{-1} + k_2) c$. Let $K_S = k_{-1}/k_1$, $K_M = (k_{-1}+k_2)/k_1$ and the Van Slyke–Cullen constant $K = k_2/k_1 = K_M - K_S$. Dropping the quadratic terms gives the linear system

$$\begin{pmatrix}\dot s\\ \dot c\end{pmatrix} = \begin{pmatrix} -k_1 e_0 & k_{-1}\\ k_1 e_0 & -(k_{-1} + k_2)\end{pmatrix}\begin{pmatrix} s\\ c\end{pmatrix},$$

whose solution $(s^*, c^*)$ is an explicit sum of two exponentials with rates $\frac{k_1}{2}\bigl((K_M + e_0) \mp \sqrt{(K_M - e_0)^2 + 4K_S e_0}\bigr)$.

**Theorem.**
1. *(Sandwich.)* Let $(s_{\mathrm{low}}, c_{\mathrm{low}})$ be the explicit solution with $K_M$ replaced by $K_M + s_0$, and $(s_{\mathrm{up}}, c_{\mathrm{up}})$ the one with $K_S$ replaced by $K_S + s_0$. If $s_0 < K$, then for all $t \ge 0$

$$s_{\mathrm{low}} \le s, s^* \le s_{\mathrm{up}}, \qquad c_{\mathrm{low}} \le c, c^* \le c_{\mathrm{up}} .$$

2. *(Uniform error.)* For parameters $(e_0, k_1, k_{-1}, k_2)$ in a compact subset of the positive orthant, with $K^* = \min k_2/k_1$ over it, there is a constant $C$ such that for $0 < s_0 \le K^*/2$ and all $t \ge 0$

$$\Bigl|\frac{s - s^*}{s_0}\Bigr| \le C s_0, \qquad \Bigl|\frac{c - c^*}{s_0}\Bigr| \le C s_0 .$$

Thus $s_0 \ll K$ suffices for pseudo-first-order kinetics, independently of $e_0$.
3. *(Timescale separation within the linear system.)* When the two eigenvalues are well separated, the slow eigenvalue is approximately $-k_2 e_0/(K_M + e_0)$, the reduced equation is $\frac{d}{dt}(s, c) = -\frac{k_2 e_0}{K_M + e_0}(s, c)$, and the slow eigenspace is asymptotic to the span of $\bigl(K_M - \frac{K e_0}{K_M + e_0},\ e_0\bigr)$.

## Depends on

- [Rigorous QSSA](../../michaelis-menten-kinetics-and-the-quasi-steady-s/abs-sub-reduced-le.md)

## Expansion

On a convex positively invariant region with $0 \le s \le s_0$ and $c < e_0$ the Michaelis–Menten vector field is cooperative (nonnegative off-diagonal Jacobian entries), and it lies between the two linear fields obtained by bounding the quadratic terms using $0 \le s \le s_0$. Kamke's comparison theorem for cooperative systems then traps the true solution between the two explicit linear solutions, and their difference is $O(s_0^2)$ uniformly in time. Unlike the standard quasi-steady-state reduction, the linear approximation is valid with or without fast–slow separation; when separation is present it reduces further to a single exponential decay at the familiar rate $k_2 e_0/(K_M + e_0)$.

## Sources

- J. Eilertsen, S. Schnell, S. Walcher, "The Michaelis–Menten reaction at low substrate concentrations: Pseudo-first-order kinetics and conditions for timescale separation", *Bulletin of Mathematical Biology* 86(6) (2024), 68, Propositions 1, 2 and 3, <https://doi.org/10.1007/s11538-024-01295-z> (preprint arXiv:2403.05507).
