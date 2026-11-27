# Ott–Antonsen invariant manifold for globally coupled phase oscillators

For the continuum limit of the Kuramoto model of globally coupled phase oscillators, and the extensions treated by Ott and Antonsen (2008), describe the state by a density $f(\omega, \theta, t)$ of oscillators with natural frequency $\omega$, distributed with density $g$, and phase $\theta$. The source considers densities of the form

$$f = \frac{g(\omega)}{2\pi}\Bigl[1 + \sum_{n \ge 1}\bigl(\alpha(\omega, t)^n e^{in\theta} + \text{c.c.}\bigr)\Bigr],$$

(the series is unnumbered in the source), for which the evolution equation reduces to the single equation $\partial_t\alpha + (K/2)(r\alpha^2 - r^*) + i\omega\alpha = 0$ (Eq. (6)), independent of the Fourier mode, where $r$ is the order parameter. The series converges, to the Poisson kernel $\frac{g(\omega)}{2\pi}\,\frac{1 - |\alpha|^2}{|1 - \alpha e^{i\theta}|^2}$ (the summed form, Eq. (8)), exactly when $|\alpha| < 1$; the case $|\alpha| = 1$ gives no density, only a Dirac measure in $\theta$ as a weak limit. The source shows that Eq. (6) leaves the circle $|\alpha| = 1$ invariant for real $\omega$ (Eq. (9)), so $|\alpha| < 1$ is preserved. Let $M$ be the set of such densities with $|\alpha(\omega, t)| < 1$ for real $\omega$ and $\alpha$ analytically continuable into the lower half $\omega$-plane, without singularities there and with $|\alpha| \to 0$ as $\operatorname{Im}\omega \to -\infty$; these conditions are preserved by Eq. (6), so $M$ is invariant under the dynamics. For a Lorentzian $g$ the order parameter on $M$ obeys a closed low-dimensional ordinary differential equation (Eq. (10) for $\rho = |r|$, with constant phase, for the Lorentzian centered at $0$ with half-width $1$; Eq. (14) is the corresponding equation for the extension with external forcing), which gives an exact solution for the macroscopic nonlinear dynamics of the Kuramoto model.

## Expansion

1. The model: the continuity equation for $f$, the order parameter and the coupling term, for the Kuramoto model and each extension separately.
2. Substitution of the series ansatz: one equation (6) for $\alpha$, the same for every Fourier mode, invariance of $|\alpha| = 1$ (Eq. (9)) and hence preservation of $|\alpha| < 1$; the Poisson-kernel form of the density for $|\alpha| < 1$.
3. The analyticity conditions in the lower half plane, their preservation in time, and the residue evaluation of the order parameter.
4. The Lorentzian case: the order-parameter equation (10), its fixed points (incoherence and partial locking) and the Kuramoto critical coupling.
5. What is not claimed: that every initial density converges to $M$; the source's comparison of attractors on $M$ with those of the full dynamics is numerical.

## Sources

- E. Ott and T. M. Antonsen, Low dimensional behavior of large systems of globally coupled oscillators, Chaos 18 (2008), 037113, Eqs. (6), (8), (9), (10), (14). <https://arxiv.org/abs/0806.0004>
