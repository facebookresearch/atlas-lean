# Equilibrium-set stability of the acute target-cell-limited model

Let $U, I, V \ge 0$ be uninfected target cells, infected cells and free virus, with infection rate $\beta > 0$, infected-cell death rate $\delta > 0$, virion production rate $p > 0$ and virion clearance rate $c > 0$:

$$\dot U = -\beta U V, \qquad \dot I = \beta U V - \delta I, \qquad \dot V = p I - c V,$$

on the invariant set $\mathcal X = \mathbb{R}^3_{\ge 0}$. Define the critical target-cell level $U_c = \delta c/(\beta p)$, the instantaneous within-host reproduction number $\mathcal R(t) = \beta p\, U(t)/(c\delta) = U(t)/U_c$, and $R_0 = \mathcal R(0)$. Every point $(U_s, 0, 0)$ is an equilibrium; let

$$\mathcal X_{s} = \{(U, 0, 0) : U \ge 0\}, \qquad \mathcal X_{s1} = \{(U, 0, 0) : 0 \le U < U_c\}.$$

**Theorem.**
1. (Linearization) At $(U_s,0,0)$ the Jacobian has eigenvalues $0$ and $\lambda_{2,3} = \tfrac12\big(-(c+\delta) \pm \sqrt{(c+\delta)^2 + 4c\delta(U_s/U_c - 1)}\big)$, so the transverse eigenvalues are both negative when $U_s < U_c$ and one is positive when $U_s > U_c$.
2. (Convergence) From any initial state with $U(0) > 0$, $V(0) > 0$, $U(t)$ decreases to a limit $U_\infty < U(0)$ and $I(t), V(t) \to 0$; thus $\mathcal X_s$ is attractive.
3. (Asymptotic stability of the set) Each point of $\mathcal X_{s1}$ is Lyapunov stable, and $\mathcal X_{s1}$ is the smallest asymptotically stable equilibrium set, with domain of attraction $\mathcal X$. No single equilibrium is asymptotically stable.
4. (Viral spread) Starting from $U(0) = U_0 > 0$, $I(0) = 0$, $V(0) = V_0 > 0$, if the viral load ever increases then $R_0 > 1$; equivalently $R_0 < 1$ is sufficient for $V$ to decrease monotonically from the infection time.

## Expansion

Linearizing at $(U_s, 0, 0)$ decouples $U$ (zero eigenvalue along the line of equilibria) from the $(I,V)$ block $\begin{pmatrix} -\delta & \beta U_s \\ p & -c\end{pmatrix}$, whose determinant $c\delta - \beta p U_s$ changes sign exactly at $U_s = U_c$. Since $\dot U \le 0$, $U$ converges; then $UV \to 0$, and the linear equations for $I$ and $V$ force both to $0$. For Lyapunov stability of $(U_s,0,0)$ with $0 < U_s < U_c$, the function $J = U - U_s - U_s\ln(U/U_s) + I + (\delta/p)V$ satisfies $\dot J = V(\beta U_s - \delta c/p) = \beta V (U_s - U_c) \le 0$ on $\mathcal X$ (not strictly), which with the attractivity gives asymptotic stability of the set. At $t = 0$ with $I(0) = 0$ one has $\dot V(0) < 0$, and a first local maximum of $V$ requires $\beta p U > c\delta$ at some time, impossible if $U(0) < U_c$ since $U$ only decreases. Antiviral treatment that lowers $p$ or $\beta$ raises $U_c$, moving the current state into the stable set.

## Sources

- P. Abuin, A. Anderson, A. Ferramosca, E. A. Hernandez-Vargas, A. H. González, "Characterization of SARS-CoV-2 dynamics in the host", Annual Reviews in Control 50 (2020) 457–468, Eqs. (2.1)–(2.8), Definitions 1–2, Theorem 2.1, Property 1, Theorems 3.1–3.3 and Theorem 4.1, <https://doi.org/10.1016/j.arcontrol.2020.09.008>, PMCID PMC7538078.
