# Principal-eigenvalue threshold for within-host HIV with a spatially heterogeneous reproductive ratio

**Model.** On the square $\Omega_\ell = (0,\ell)^2$ with periodic boundary conditions, target CD4 cells $T$, infected cells $I$ and diffusing virions $V$ satisfy

$$T_t = \alpha(x) - \gamma V T - \mu_T T, \qquad I_t = \gamma V T - \mu_I I, \qquad V_t = N\mu_I I - \mu_V V + d_V \Delta V,$$

where the supply of target cells $\alpha(x) > 0$ varies in space (e.g. lymphoid tissue) and is piecewise continuous and $\ell$-periodic in each variable, $\gamma$ is the infection rate, $N$ the burst size, and $\mu_T, \mu_I, \mu_V, d_V > 0$. The **heterogeneous reproductive ratio** is

$$R_0(x) = \frac{\gamma N \alpha(x)}{\mu_T \mu_V};$$

sites with $R_0(x) < 1$ are sinks and sites with $R_0(x) > 1$ are sources. Let $\lambda_0$ be the largest eigenvalue of the periodic operator $d_V \Delta + \mu_V (R_0(x) - 1)$, the linearization at $V \equiv 0$ of the steady-state equation

$$d_V \Delta V - \mu_V V = -\mu_T \mu_V R_0(x)\,\frac{V}{\gamma V + \mu_T}.$$

If $R_0$ is constant, $\lambda_0 = \mu_V(R_0 - 1)$.

**Theorem.**

1. (Steady states.) If $\lambda_0 \le 0$ the uninfected state $(T_u, I_u, V_u) = (\alpha/\mu_T, 0, 0)$ is the only nonnegative steady state. If $\lambda_0 > 0$ there is exactly one more, an infected steady state $(T_i, I_i, V_i)$ with all components positive on $\overline{\Omega_\ell}$ and

$$T_i = \frac{\alpha}{\gamma V_i + \mu_T}, \qquad I_i = \frac{\gamma \alpha V_i}{\mu_I(\gamma V_i + \mu_T)}.$$

2. (Dynamics.) The uninfected state is stable if $\lambda_0 < 0$ and unstable if $\lambda_0 > 0$; for $\lambda_0 > 0$ and $\alpha \in W^{1,\infty}$ the evolution semigroup has a connected universal attractor.
3. (Homogenization.) Let $R_0^\varepsilon(x) = R_0(x/\varepsilon)$ for a fixed piecewise continuous profile $R_0$, periodic with period $1$ in each variable, with cell mean $\mathcal M_y(R_0) > 1$. Then for small $\varepsilon$ the infected viral steady state $V^\varepsilon$ exists and, as $\varepsilon \to 0$,

$$V^\varepsilon \to V^0 = \frac{\mu_T}{\gamma}\big(\mathcal M_y(R_0) - 1\big)$$

in $H^1$ and uniformly.

So infection can persist even when $R_0(x) < 1$ on most of the tissue, as long as sources make $\lambda_0$ positive; on finely mixed tissue only the average reproductive ratio matters.

## Expansion

At steady state the $T$ and $I$ equations are algebraic, giving $T_i, I_i$ in terms of $V_i$ and reducing the problem to the semilinear elliptic equation above, whose nonlinearity $V \mapsto R_0 V/(\gamma V + \mu_T)$ is concave. The variational characterization of the principal eigenvalue of the periodic Sturm–Liouville operator gives existence of a positive solution by sub- and super-solutions ($\varepsilon \phi_0$ with $\phi_0$ the positive eigenfunction, and a large constant) exactly when $\lambda_0 > 0$, and concavity gives uniqueness. Linearized stability of $V \equiv 0$ is governed by the sign of $\lambda_0$. In the homogenization limit the semilinear equation converges to its cell-averaged constant-coefficient version, whose positive root is $V^0$.

## Sources

- C.-M. Brauner, Danaelle Jolly, Luca Lorenzi, Rodolphe Thiébaut, "Heterogeneous Viral Environment in a HIV Spatial Model", arXiv (2009). Sections 1–2 (model, $R_0(x)$, $\lambda_0$), Theorems 2.1, 2.4, 3.1, 5.3. <https://doi.org/10.48550/arXiv.0905.2023>. Published version: Discrete and Continuous Dynamical Systems - B 15(3) (2011), 545–572, <https://doi.org/10.3934/dcdsb.2011.15.545>; locators above refer to the arXiv version.
