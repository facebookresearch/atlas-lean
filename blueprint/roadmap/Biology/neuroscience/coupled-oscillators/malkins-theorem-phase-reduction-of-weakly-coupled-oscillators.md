# Malkin's theorem on phase reduction of weakly coupled oscillators

Consider oscillators $\dot X_j = F(X_j) + \varepsilon\bigl[f_j(X_j) + \sum_k G_{jk}(X_j, X_k)\bigr]$, $j = 1, \dots, N$, where $\dot X = F(X)$ has an exponentially stable limit cycle $X_0(\theta)$ of frequency $\omega$, parametrized by the phase $\theta \in [0, 2\pi)$, and $\varepsilon$ is small. Nakao (2017, Section 3.4) describes the phase sensitivity function $Z(\theta)$ as the $2\pi$-periodic solution of the adjoint equation $\omega\,\frac{d}{d\theta}Z(\theta) = -J(\theta)^{T}Z(\theta)$, where $J(\theta)$ is the Jacobian of $F$ at $X_0(\theta)$, normalized by $Z(\theta)\cdot\frac{dX_0}{d\theta}(\theta) = 1$, and notes that this adjoint equation is the key part of Malkin's theorem, which justifies the phase description. In Section 5 he reduces the coupled system to the phase equations $\dot\theta_j = \omega + \varepsilon\bigl[Z(\theta_j)\cdot f_j(\theta_j) + \sum_k Z(\theta_j)\cdot G_{jk}(\theta_j, \theta_k)\bigr]$ with error $O(\varepsilon^2)$, and, averaging over one period, to
$$\dot\theta_j = \omega + \varepsilon\Bigl[\Delta_j + \sum_k \Gamma_{jk}(\theta_j - \theta_k)\Bigr], \quad \Delta_j = \frac{1}{2\pi}\int_0^{2\pi} Z(\psi)\cdot f_j(\psi)\,d\psi, \quad \Gamma_{jk}(\phi) = \frac{1}{2\pi}\int_0^{2\pi} Z(\phi + \psi)\cdot G_{jk}(\phi + \psi, \psi)\,d\psi,$$
again with error $O(\varepsilon^2)$ (Eqs. (48)–(52)), so the coupling acts only through phase differences.

## Expansion

1. The model: smooth vector fields with an exponentially stable limit cycle of a common frequency, weak heterogeneity and weak coupling.
2. The adjoint equation along the limit cycle: existence and uniqueness of the normalized periodic solution $Z$ from the simplicity of the Floquet multiplier $1$, and $Z$ as the gradient of the asymptotic phase (the infinitesimal phase response curve).
3. The reduction to phase equations and the averaging step, with the $O(\varepsilon^2)$ remainders, and Malkin's formulation of the result for time scales of order $1/\varepsilon$.
4. The coupling functions $\Gamma_{jk}$ and their dependence only on phase differences; the case of commensurable frequencies, as a separate statement.

## Sources

- H. Nakao, Phase reduction approach to synchronization of nonlinear oscillators, arXiv preprint, 2017, Section 3.4 (Eqs. (12)–(13)) and Section 5 (Eqs. (48)–(52)). <https://arxiv.org/abs/1704.03293>
- Original result: F. C. Hoppensteadt and E. M. Izhikevich, Weakly Connected Neural Networks, Springer, 1997, Ch. 9 (Malkin's theorem). <https://doi.org/10.1007/978-1-4612-1828-9> The adjoint equation and the averaged phase equations follow Nakao (2017).
