# Periodic reproduction number and the monodromy matrix

In the setting of the [next-generation operator in a periodic environment](periodic-next-generation-operator.md), let $\Phi_{F-V}(t)$ be the principal fundamental matrix of the linearized infected subsystem $\dot z = (F(t) - V(t)) z$, so that $\Phi_{F-V}(\omega)$ is its monodromy matrix.

**Theorem (Wang–Zhao).** $\mathcal{R}_0 - 1$ and $\rho\big(\Phi_{F-V}(\omega)\big) - 1$ have the same sign:

$$\mathcal{R}_0 < 1 \iff \rho\big(\Phi_{F-V}(\omega)\big) < 1, \qquad \mathcal{R}_0 = 1 \iff \rho\big(\Phi_{F-V}(\omega)\big) = 1, \qquad \mathcal{R}_0 > 1 \iff \rho\big(\Phi_{F-V}(\omega)\big) > 1.$$

## Depends on

- [Next-generation operator in a periodic environment](periodic-next-generation-operator.md)

## Expansion

For $\lambda > 0$ let $W_\lambda(t)$ be the principal fundamental matrix of $\dot z = (F(t)/\lambda - V(t)) z$. The function $\lambda \mapsto \rho(W_\lambda(\omega))$ is continuous and nonincreasing and tends to $\rho(Y(\omega, 0)) < 1$ as $\lambda \to \infty$, and, when $\mathcal{R}_0 > 0$, $\mathcal{R}_0$ is the unique $\lambda$ at which it equals $1$; comparing with $\lambda = 1$ gives the three equivalences. For constant coefficients $\rho(\Phi_{F-V}(\omega)) = e^{s(F - V)\omega}$ with $s$ the spectral abscissa, and the theorem reduces to the autonomous threshold of [$R_0$ for the linearized infected subsystem](is-hurwitz-sub-iff-r0-lt-one.md).

## Sources

- W. Wang, X.-Q. Zhao, "Threshold dynamics for compartmental epidemic models in periodic environments", Journal of Dynamics and Differential Equations 20 (2008) 699–717, <https://doi.org/10.1007/s10884-008-9111-8>, Theorem 2.2.
