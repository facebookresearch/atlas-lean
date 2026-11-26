# Periodic solutions of the delayed tumor–effector model under weak periodic chemotherapy

**Setting.** Consider the delayed tumor–effector system

$$
\begin{aligned}
\dot T(t) &= T(t)\,r\Big[\frac{1-T(t)^{\beta}}{\beta} - b(t)\Big] - \gamma E(t)T(t),\\
\dot E(t) &= \sigma + \frac{p\,E(t)\,T(t-\tau_1)}{g + a\,T(t-\tau_1)} - \frac{m\,E(t)\,T(t-\tau_2)}{g + a\,T(t-\tau_2)} - \eta E(t),
\end{aligned}
$$

with positive coefficients, $0<\beta\le 1$, and a chemotherapy term $b(t)=b_0+\varphi(t)$, where $b_0$ is a constant and $\varphi$ is continuous and $\omega$-periodic. Let $(T^*,E^*)$ be an admissible equilibrium of the autonomous undelayed system ($\varphi\equiv 0$, $\tau_1=\tau_2=0$), and let $M$ be the Jacobian of its right-hand side at $(T^*,E^*)$.

**Theorem (continuation of equilibria to periodic solutions).** Assume that $M$ has no eigenvalue of the form $\pm 2k\pi i/\omega$ with $k\in\{0,1,2,\dots\}$. Then there are constants $\varphi^*,\tau_1^*,\tau_2^*,r^*>0$ such that, whenever $\|\varphi\|_\infty<\varphi^*$, $\tau_1<\tau_1^*$ and $\tau_2<\tau_2^*$, the system has at least one $\omega$-periodic solution $(T,E)$ with $\|(T-T^*,E-E^*)\|_\infty<r^*$; this solution depends smoothly on $(\varphi,\tau_1,\tau_2)$.

**Verification of the hypothesis.** At the tumor-free equilibrium $(0,\sigma/\eta)$ the matrix $M$ is lower triangular with real eigenvalues $r(1-\beta b_0)/\beta-\gamma\sigma/\eta$ and $-\eta$, so the hypothesis holds whenever the first eigenvalue is nonzero. At a positive equilibrium, $\operatorname{tr} M = -r\beta (T^*)^{\beta}-\sigma/E^*<0$, which excludes nonzero purely imaginary eigenvalues; the hypothesis then reduces to $\det M\ne 0$.

## Expansion

Write the system as $X'=\Phi(X,y)$ on the space $C_\omega$ of continuous $\omega$-periodic functions, with parameter $y=(\varphi,\tau_1,\tau_2)$ and shift operators $X\mapsto X(\cdot-\tau_j)$. At $y=0$ the constant function $X_0=(T^*,E^*)$ is a solution, and the linearized operator $Z\mapsto Z'-MZ$ from $C^1_\omega$ to $C_\omega$ is injective exactly when $M$ has no eigenvalue $\pm 2k\pi i/\omega$; by the Fredholm alternative it is then an isomorphism. The implicit function theorem yields a unique smooth branch $y\mapsto X(y)$ of $\omega$-periodic solutions with $X(0)=X_0$. Thus weak periodic chemotherapy and short immune delays deform both the tumor-free state and a hyperbolic tumor-present state into nearby periodic regimes with the period of the treatment, for every period $\omega$ meeting the nonresonance condition.

## Depends on

- [Equilibria and tumor-free threshold of the delayed tumor–effector model](equilibria-and-tumor-free-threshold-of-the-delayed-tumor-effector-model.md)

## Sources

- P. Amster, A. Rivera, J. A. Arredondo, *Periodic solutions in a tumor-immune competition system with time-delay and chemotherapy effects*, arXiv:2510.11135 (2025). <https://doi.org/10.48550/arXiv.2510.11135> — Theorem 3 (implicit-function continuation), Lemma 4 (nonresonance criterion), Theorem 16 (Section 5, periodic solutions near equilibria).
