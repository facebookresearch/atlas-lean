# Convergence of the JKO scheme to the Fokker–Planck equation

Let $\Psi : \mathbb{R}^n \to \mathbb{R}$ be smooth with $\Psi \ge 0$ and
$|\nabla \Psi| \le C(\Psi + 1)$, let $\beta > 0$, and let $F(\rho) = \int \Psi \rho + \beta^{-1} \int \rho \log \rho$
be the free energy. Let $\rho_0$ be an absolutely continuous probability measure with finite second
moment and finite free energy. For $h > 0$ let $\rho_h^{(k)}$ be the JKO sequence started at
$\rho_0$, where each $\rho_h^{(k)}$ minimises $\frac12 W_2(\rho_h^{(k-1)}, \rho)^2 + h F(\rho)$ over
such measures, and let $\rho_h(t) = \rho_h^{(k)}$ for $t \in [kh, (k+1)h)$. Then, as $h \downarrow 0$,
$\rho_h(t)$ converges weakly in $L^1$ to $\rho(t)$ for every $t > 0$, where $\rho$ is smooth on
$(0, \infty) \times \mathbb{R}^n$, solves

$$\partial_t \rho = \operatorname{div}(\rho \nabla \Psi) + \beta^{-1} \Delta \rho,$$

satisfies $\rho(t) \to \rho_0$ in $L^1$ as $t \downarrow 0$, and has second moment and potential energy in
$L^\infty(0, T)$ for every $T > 0$.

## Idea

Jordan, Kinderlehrer and Otto showed that the Fokker–Planck equation is the gradient flow of the
free energy for the quadratic Wasserstein distance, made precise by this implicit time
discretisation. Each step balances decreasing the free energy against moving far in $W_2$. The
first variation of a step is a time-discrete weak form of the equation, the discrete energy
inequality gives the compactness needed to pass to the limit, and the limit solves the equation.
When $Z = \int e^{-\beta\Psi}$ is finite, the Gibbs density $Z^{-1} e^{-\beta \Psi}$ is a
stationary solution of the equation; if it is admissible and has finite free energy, it minimises
the free energy among admissible densities of finite energy and entropy.

## Statements

- [Convergence of the JKO scheme to the Fokker–Planck equation](tendsto-jko-fokker-planck.md)
- [Free energy of the Fokker–Planck equation](free-energy.md): a definition used in the statement.
- [Negative Boltzmann entropy](neg-entropy.md): part of the free energy.
- [Potential energy](potential-energy.md): part of the free energy.
- [Admissible densities of the JKO scheme](is-admissible.md): a definition used in the statement.
- [JKO objective](jko-objective.md): a definition used in the statement.
- [JKO step](is-jkostep.md): a definition used in the statement.
- [JKO sequence](is-jkosequence.md): a definition used in the statement.
- [Existence and uniqueness of the JKO step](exists-unique-is-jkostep.md): the scheme is well defined.
- [The JKO objective at the previous state](jko-objective-self.md): a basic fact of the objective.
- [One-step comparison inequality of the JKO scheme](jko-objective-le.md): a basic fact of a step.

## Background

- [Minimizing-movement scheme](../minimizing-movements/README.md): the scheme in a general metric space.
- [Wasserstein distance](../../wasserstein-distances/wasserstein-distance/README.md): the distance $W_2$.

## Sources

- R. Jordan, D. Kinderlehrer and F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998).
