# Regular graphons minimize the reproduction number at fixed mean degree

Consider the [kernel SIS model](threshold-theorem-for-the-kernel-sis-model.md) on a probability space $(\Omega, \mathscr F, \mu)$ with transmission kernel in graphon form

$$\kappa(x, \mathrm dy) = \beta\,W(x,y)\,\theta\,\mu(\mathrm dy),$$

where $W : \Omega \times \Omega \to [0,1]$ is a symmetric measurable graphon and the susceptibility $\beta > 0$, infectiousness $\theta > 0$ and recovery rate $\gamma > 0$ are constants. Write $\deg_W(x) = \int_\Omega W(x,y)\,\mu(\mathrm dy)$ and $d_W = \int_\Omega \deg_W\,d\mu$ for the mean degree, and $R_0[W] = r(T_{k/\gamma})$ with $k = \beta W \theta$.

**Corollary.** Fix $p \in [0,1]$. Among all graphons $W$ with mean degree $d_W \ge p$, the smallest value of $R_0[W]$ is attained by graphons of constant degree $\deg_W \equiv p$, for which

$$R_0[W] = \frac{\beta\,\theta\,p}{\gamma}.$$

So, at a given average contact intensity, degree heterogeneity can only raise the reproduction number; the homogeneous (regular) contact structure is the least favorable to an outbreak.

## Expansion

For symmetric $W$ the operator $T_W$ is self-adjoint on $L^2(\mu)$, and by the Rayleigh quotient with test function $\mathbf 1$, $r(T_W) \ge \langle \mathbf 1, T_W \mathbf 1\rangle / \langle \mathbf 1, \mathbf 1 \rangle = d_W$. If $\deg_W \equiv p$, then $T_W \mathbf 1 = p\,\mathbf 1$ with a positive eigenfunction, so $r(T_W) = p$ by the Collatz–Wielandt inequality and its converse. Multiplying by the constant $\beta\theta/\gamma$ gives the claim. This comparison feeds the paper's study of vaccination and lockdown, where the reproduction number is optimized over the remaining contact structure.

## Sources

- Jean-François Delmas, Dylan Dronnier, Pierre-André Zitt, "An Infinite-Dimensional SIS Model", arXiv (2020). Corollary 1.8; Lemma 6.2 (degree bounds on $R_0$), Proposition 3.3 (Collatz–Wielandt inequality). <https://doi.org/10.48550/arXiv.2006.08241>. Published version: Journal of Differential Equations 313 (2022), 1–53, <https://doi.org/10.1016/j.jde.2021.12.024>; locators above refer to the arXiv version.
