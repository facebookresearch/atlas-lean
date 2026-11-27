# Boundary classification of the Wright–Fisher diffusion with mutation

For the Wright–Fisher diffusion $Lf = \frac12x(1 - x)f'' + [\sigma x(1 - x) + \frac12(\theta_1(1 - x) - \theta_2x)]f'$ with $\sigma$ real and $\theta_1, \theta_2 \ge 0$, the endpoint $0$ is an exit boundary when $\theta_1 = 0$, a regular boundary when $0 < \theta_1 < 1$, and an entrance boundary when $\theta_1 \ge 1$; the same holds at $1$ with $\theta_2$ in place of $\theta_1$, and $\sigma$ does not affect the classification.

The proof is a computation with Feller's accessibility and enterability integrals. The scale density is $\psi(x) = e^{-2\sigma x}x^{-\theta_1}(1 - x)^{-\theta_2}$ and the speed density $m(x) = 2e^{2\sigma x}x^{\theta_1 - 1}(1 - x)^{\theta_2 - 1}$; near $0$ the factors $e^{\pm2\sigma x}$ and $(1 - x)^{\pm\theta_2}$ are bounded above and below, so only the powers of $x$ matter. With $S(y) = \int_c^y\psi$ and $c = \frac12$:

- If $\theta_1 \ge 1$, $S(y) \to -\infty$ as $y \downarrow 0$, so $0$ is not accessible. The enterability integral $\int_0^c(S(c) - S(y))m(y)\,dy$ is finite, since $S(c) - S(y)$ grows like $\log(1/y)$ for $\theta_1 = 1$ and like $y^{1 - \theta_1}$ for $\theta_1 > 1$, while $m(y)$ behaves like $y^{\theta_1 - 1}$. Hence $0$ is an entrance boundary.
- If $0 < \theta_1 < 1$, $S(0)$ is finite and $m$ is integrable at $0$, so both $\int_0^c(S(y) - S(0))m(y)\,dy$ and the enterability integral are finite: $0$ is regular.
- If $\theta_1 = 0$, $S(y) - S(0)$ is of order $y$ and $m(y)$ of order $1/y$, so the accessibility integral is finite, while $S(c) - S(y)$ tends to $S(c) - S(0) > 0$ and $\int_0m(y)\,dy = \infty$: $0$ is an exit boundary.

This agrees with Jenkins and Spanò (2017, Section 1), who note that the boundaries of the Wright–Fisher diffusion can be exit, regular reflecting or entrance depending on the drift parameters. Song and Steinrücken (2012, section on the neutral diffusion with recurrent mutation) likewise note that under recurrent mutation the boundaries are regular or entrance.

## Depends on

- [Feller's boundary classification](../../../../Probability/stochastic-calculus/one-dimensional-diffusions/feller-boundary-classification.md)
- [Scale density with selection and mutation](../../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/selection-mutation-scale-density.md)
- [Speed density with selection and mutation](../../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/selection-mutation-speed-density.md)

## Expansion

1. The local behaviour of $\psi$, $S$ and $m$ near $0$, with the bounded factors separated.
2. The accessibility integral at $0$: finite exactly when $\theta_1 < 1$.
3. The enterability integral at $0$: finite exactly when $\theta_1 > 0$.
4. The classification at $1$ by the symmetry $x \mapsto 1 - x$, $\theta_1 \leftrightarrow \theta_2$, $\sigma \mapsto -\sigma$.
5. For $0 < \theta_1 < 1$, identification of the limit of Wright–Fisher chains with mutation as the instantaneously reflecting extension at $0$, as a separate statement.

## Sources

- P. A. Jenkins and D. Spanò, Exact simulation of the Wright–Fisher diffusion, Ann. Appl. Probab. 27 (2017), 1478–1509, Section 1. <https://doi.org/10.1214/16-AAP1236>
- Y. S. Song and M. Steinrücken, A simple method for finding explicit analytic transition densities of diffusion processes with general diploid selection, Genetics 190 (2012), 1117–1129, section on diffusions with recurrent mutation. <https://doi.org/10.1534/genetics.111.136929>
