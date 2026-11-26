# Unique stable equilibrium of the zeroth-order actin branching model

In the zeroth-order branching model (generalizing Weichsel and Schwarz), the filament orientation density $u(\theta,t) \ge 0$ on $S^1$ satisfies

$$
\partial_t u(\theta,t) = \frac{b}{\int_{S^1} u(\omega,t)\,d\omega}\,(\mathcal{B} \star u)(\theta,t) - \kappa(\theta)\,u(\theta,t),
$$

with total branching rate $b > 0$ independent of the number of filaments, a real, positive, symmetric $C^2$ kernel $\mathcal{B}$ with $\|\mathcal{B}\|_1 = 1$, and a real, strictly positive, symmetric $C^2$ capping rate $\kappa$.

**Theorem.** For non-negative initial data in $L^1(S^1)$ the equation has a global solution. A function $u \in L^1$ is an equilibrium if and only if it solves the eigenvalue problem

$$
\frac{\mathcal{B} \star u}{\kappa(\theta)} = \mu\,u(\theta), \qquad \mu \ne 0, \quad \int_{S^1} u \ne 0 ,
$$

so there is a unique positive equilibrium $u_0$ (the positive eigenfunction, scaled so that $\int u_0 = b\mu$), and the spectral bound of the linearization at $u_0$ is strictly negative: $u_0$ is locally asymptotically stable.

## Expansion

The nonlinearity $u \mapsto b(\mathcal{B}\star u)/\int u$ is homogeneous of degree one, so equilibria are scale-fixed eigenfunctions of the positive compact operator $u \mapsto (\mathcal{B} \star u)/\kappa$, and Krein–Rutman gives uniqueness of the positive one. Local Lipschitz bounds on sets where $\int u$ stays between two positive constants give global existence. In the linearization the normalization term removes the neutral direction, and a resolvent estimate shows that no spectrum lies in the closed right half-plane. Thus, like the [linear model](principal-eigenfunction-selection-in-the-linear-actin-branching-model.md), the nonlinear model selects a single dominant orientation pattern, now without tuning the branching rate.

## Sources

- Daniel Smith and Jian Liu, *Nonlocal actin orientation models select for a unique orientation pattern*, arXiv:1301.6137, Section 3 ("Zeroth-order Branching"), existence proposition, equilibrium characterization and the stability theorem for the linearization. <https://doi.org/10.48550/arXiv.1301.6137>
