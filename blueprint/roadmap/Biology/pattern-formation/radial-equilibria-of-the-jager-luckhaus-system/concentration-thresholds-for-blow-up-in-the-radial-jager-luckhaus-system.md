# Concentration thresholds for blow-up in the radial Jäger–Luckhaus system

**Setting.** Consider the Jäger–Luckhaus system $u_t=\Delta u-\nabla\cdot(u\nabla v)$, $0=\Delta v-\mu+u$ on the unit disk with no-flux boundary conditions, mass $M=\int u_0$, $\mu=M/\pi$, and $\Lambda=j_{1,1}^2$ (square of the first positive zero of $J_1$). For nonnegative radial densities $f,g$ define the cumulative mass $F_f(\xi)=\int_{|x|<\sqrt\xi}f\,dx$, $\xi\in[0,1]$, and the **concentration order**: $f\succeq g$ ($f$ more concentrated than $g$) if $F_f(\xi)\ge F_g(\xi)$ for all $\xi\in[0,1]$.

**Threshold equilibria.** Call a radial equilibrium $u_*$ of mass $M$ a threshold equilibrium if it is (a) the decreasing equilibrium when $8\pi<M<\Lambda\pi$, (b) the constant state $\mu$ when $M\ge\Lambda\pi$, or (c) any non-monotone radial equilibrium.

**Theorem (sharp concentration threshold).** Let $u_*$ be a threshold equilibrium of mass $M$ and let $u_0$ be continuous, nonnegative and radial with the same mass.

- If $u_0\succeq u_*$ and $u_0\ne u_*$, the solution blows up in finite time.
- If $u_0\preceq u_*$, the solution is global and uniformly bounded; if also $u_0\ne u_*$, then $u(t)\to\underline u_M$ in $L^\infty$ (and $v(t)\to\underline v_M$ in $W^{1,\infty}$), where $\underline u_M$ is the least concentrated equilibrium: the constant $\mu$ for $M\le\Lambda\pi$ and the increasing equilibrium for $M>\Lambda\pi$.

For $0<M\le 8\pi$ every radial solution is global and converges to $\mu$.

**Least concentrated equilibrium and stability.** For $M>\Lambda\pi$ the increasing equilibrium $u_M^{\mathrm i}$ satisfies $F_u>F_{u_M^{\mathrm i}}$ on $(0,1)$ for every other radial equilibrium $u$ of mass $M$, and any two other equilibria are incomparable. For every $M\ne\Lambda\pi$, $\underline u_M$ is locally asymptotically stable under radial mass-preserving perturbations in $C(\overline\Omega)$ and is the only radially stable equilibrium; it is globally asymptotically stable for $M\le 8\pi$. At $M=\Lambda\pi$ the constant state is the unique radial equilibrium and is nonlinearly unstable. All threshold equilibria are nonlinearly unstable.

## Depends on

- [Classification of radial equilibria of the Jäger–Luckhaus system on the disk](classification-of-radial-equilibria-of-the-jager-luckhaus-system-on-the-disk.md)

## Expansion

In the cumulative variable $F(\xi,t)$ the radial system becomes a scalar degenerate parabolic equation satisfying a comparison principle, so the order $\succeq$ is preserved by the flow. Data below a threshold equilibrium are trapped below it and, being ordered, converge to the least element. For data above, one linearizes at $u_*$, takes the positive principal eigenfunction $\psi_*$ of the adjoint cumulative linearization (with $\psi_*(1)=0$, $\psi_*'<0$), and shows that the $\psi_*$-weighted moment of $F-F_*$ satisfies a superlinear differential inequality, which forces blow-up in finite time. The equilibria are thus the exact boundaries between collapse and bounded redistribution at fixed total population.

## Sources

- Xuan Mao, Wanwan Wang, "Unstable radial equilibria as sharp concentration thresholds for the Jäger–Luckhaus model on the unit disk", arXiv:2610.39209 (2026), Theorem 1.3, Theorem 1.4, Corollary 1.5, Theorem 1.6 and Corollary 1.7, <https://doi.org/10.48550/arXiv.2610.39209>.
