# ACR systems reject persistent disturbances orthogonal to a linear integrator

Let $\dot x = f(x) = Y A(\kappa)\Lambda(x)$ be a mass-action system with complexes $y_i, y_j$ for which the set $\hat\Gamma_{ij}(\kappa)$ of [linear constrained integrators](linear-constrained-integrators-of-acr-mass-action-systems.md) is non-empty, so that there is $\bar q \ge 0$ with $c^{y_j - y_i} = \bar q$ for all steady states $c$ with $c^{y_i} \ne 0$. Perturb the dynamics by an arbitrary time-varying input $u : \mathbb{R}^d_{\ge0} \times \mathbb{R}_{\ge 0} \to \mathbb{R}^d$,

$$
\frac{d}{dt}\tilde x(t) = f(\tilde x(t)) + u(\tilde x(t), t),
$$

with a solution satisfying $\tilde x(t) \ge 0$ for all $t \ge 0$.

**Theorem.** Suppose some $\hat\gamma \in \hat\Gamma_{ij}(\kappa)$ is orthogonal to $u(x,t)$ for all $x \in \mathbb{R}^d_{\ge 0}$ and $t \ge 0$. Then for every initial condition at least one of the following holds:

1. some species $X_k$ in the support of $\hat\gamma$ has $\limsup_{t\to\infty} \tilde x_k(t) = \infty$;
2. some species $X_k$ in the support of $y_i$ has $\liminf_{t\to\infty} \tilde x_k(t) = 0$;
3. $\tilde x(t)^{y_j - y_i}$ oscillates around $\bar q$;
4. $\lim_{t\to\infty} \int_t^\infty \big|\tilde x(s)^{y_j - y_i} - \bar q\big|\,ds = 0$.

The same conclusion transfers to a larger reaction network containing the mass-action system as a sub-system, provided the reaction vectors of the extra reactions are orthogonal to $\hat\gamma$.

## Depends on

- [Linear constrained integrators of mass-action systems with absolute concentration robustness](linear-constrained-integrators-of-acr-mass-action-systems.md)

## Expansion

Orthogonality removes the disturbance from the integrator: $\frac{d}{dt}\langle\hat\gamma, \tilde x\rangle = \tilde x^{y_i}(\tilde x^{y_j-y_i} - \bar q)$ still holds. If neither blow-up nor extinction of the relevant species occurs, $\langle \hat\gamma, \tilde x \rangle$ stays bounded and $\tilde x^{y_i}$ stays away from $0$, so the integrated tracking error is finite and the output either converges in this integrated sense or crosses the set point infinitely often. This is the robust perfect adaptation property of integral feedback, here obtained without any designed controller.

## Sources

- Daniele Cappelletti, Ankit Gupta and Mustafa Khammash, *A hidden integral structure endows Absolute Concentration Robust systems with resilience to dynamical concentration disturbances*, arXiv:1910.05531, Section 6 and Theorem D.3 and Corollary D.4 (Appendix D). <https://doi.org/10.48550/arXiv.1910.05531> Published version: Journal of The Royal Society Interface 17 (2020) 20200437, <https://doi.org/10.1098/rsif.2020.0437>.
