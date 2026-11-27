# Principal-eigenvalue threshold for viral clearance in the diffusive target-cell model

**Setting.** On a bounded smooth domain $\Omega \subset \mathbb{R}^n$, consider the spatially heterogeneous in-host model

$$\partial_t T - D_T \Delta T = \lambda(x) - \mu_T T - kTV, \quad \partial_t I - D_I \Delta I = kTV - \mu_I I, \quad \partial_t V - D_V \Delta V = N\mu_I I - \mu_V V,$$

with all parameters positive, $\lambda \ge 0$ smooth and not identically zero, and homogeneous Dirichlet or Neumann boundary conditions. The **viral clearance state** is $E_c = (T_\infty(x), 0, 0)$, where $T_\infty$ solves

$$-D_T \Delta T_\infty = \lambda(x) - \mu_T T_\infty$$

with the same boundary conditions. Then $T_\infty$ is smooth, not identically zero, and $0 \le T_\infty(x) \le \|\lambda\|_\infty/\mu_T$.

**Principal eigenvalue.** Linearizing about $E_c$, the $(I, V)$ equations decouple and are governed by the operator $\mathcal{L} = \nabla \cdot (D\nabla) + M(x)$ with

$$D = \mathrm{diag}(D_I, D_V), \qquad M(x) = \begin{pmatrix} -\mu_I & kT_\infty(x) \\ N\mu_I & -\mu_V \end{pmatrix}.$$

The matrix $M(x)$ is not symmetric, so $\mathcal L$ is not self-adjoint; but $M(x)$ is cooperative (its off-diagonal entries are nonnegative), so the spectral bound $\eta_0 = \sup\{\operatorname{Re}\mu : \mu \in \sigma(\mathcal L)\}$ is a real principal eigenvalue of $\mathcal L$ with a positive eigenfunction. Define the local reproduction ratio

$$R_0(x) = \frac{N k T_\infty(x)}{\mu_V}.$$

For constant $\lambda$ under Neumann boundary conditions one has $T_\infty = \lambda/\mu_T$, $R_0 = \lambda k N/(\mu_T\mu_V)$ is the classical basic reproductive ratio, and $\eta_0$ is the largest eigenvalue of the constant matrix $M$,

$$\eta_0 = \tfrac12\Big(-(\mu_I + \mu_V) + \sqrt{(\mu_I - \mu_V)^2 + 4\mu_I\mu_V R_0}\Big),$$

which has the sign of $R_0 - 1$ but is not equal to $R_0 - 1$ (for $\mu_I = \mu_V = 1$, $kT_\infty = 2$, $N = 1$: $R_0 = 2$, $\eta_0 = \sqrt2 - 1$). (The source's remarks call $\mathcal L$ self-adjoint and write $\eta_0 = R_0 - 1$; its theorems use $\eta_0$ as the spectral bound, as here.)

**Theorem (uniqueness).** If $\eta_0 < 0$, then $E_c$ is the unique non-negative steady state.

**Theorem (local stability).** If $\eta_0 < 0$, $E_c$ is locally asymptotically stable; if $\eta_0 > 0$, it is unstable.

**Theorem (target cells).** For every solution and every $t \ge 0$,

$$\|T(t) - T_\infty\|_\infty \le \|T_0 - T_\infty\|_\infty\, e^{-\mu_T t}.$$

**Theorem (global clearance).** If $\|R_0\|_\infty < 1$, there are $C_0, a > 0$ with $\|I(t)\|_\infty + \|V(t)\|_\infty \le C_0 e^{-at}$ for all $t \ge 0$; together with the previous estimate, $E_c$ is globally asymptotically stable with exponential decay.

**Corollary (computable criterion).** If $N k \|\lambda\|_\infty/(\mu_T \mu_V) < 1$, the conclusion of the global clearance theorem holds.

All conclusions are independent of the diffusion coefficients and of the dimension.

## Depends on

- [Positivity and global existence for the diffusive target-cell model](positivity-and-global-existence-of-the-diffusive-target-cell-model.md)

## Expansion

The sign of the spectral bound $\eta_0$ decides linear stability, since the $T$ equation of the linearization is a damped heat equation. When $\|R_0\|_\infty < 1$, i.e. $\det(-M(x)) = \mu_I(\mu_V - NkT_\infty(x)) > 0$ for all $x$, a constant vector $v = (1, v_2)$ with $N\mu_I/\mu_V < v_2 < \mu_I/(k\|T_\infty\|_\infty)$ satisfies $M(x)v < 0$ componentwise and uniformly in $x$, so it is a strict supersolution of the cooperative linear problem and $\eta_0 < 0$; the global clearance theorem proves decay of $I$ and $V$ under this condition through sup-norm estimates on the full nonlinear system, using the boundedness of $T$. The estimate on $T - T_\infty$ comes from the heat semigroup with damping $\mu_T$. The corollary follows from $T_\infty \le \|\lambda\|_\infty/\mu_T$. The authors leave open whether $\eta_0 < 0$ alone implies global stability.

## Sources

- S. Pankavich and C. Parkinson, "Mathematical analysis of an in-host model of viral dynamics with spatial heterogeneity", arXiv:1508.07617 (2015), Section 2.3: Theorem 2.4 (properties of $T_\infty$), Theorem 2.5 (uniqueness), Theorem 2.6 (local stability), Theorem 2.7 (exponential convergence of target cells), Theorem 2.8 and Corollary 2.9 (global clearance); proofs in Section 3. <https://doi.org/10.48550/arXiv.1508.07617>. Published version: Discrete and Continuous Dynamical Systems - B 21(4) (2016), 1237–1257, <https://doi.org/10.3934/dcdsb.2016.21.1237>; locators above refer to the arXiv version.
