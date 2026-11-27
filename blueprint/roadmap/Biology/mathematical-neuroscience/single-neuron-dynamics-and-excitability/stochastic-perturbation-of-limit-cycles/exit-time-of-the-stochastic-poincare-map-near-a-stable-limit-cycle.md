# Exit time of the stochastic Poincaré map near a stable limit cycle

**Setting.** Consider an autonomous system $\dot y=f(y)$ in $\mathbb R^n$ with an exponentially stable periodic orbit $\mathcal O$ of period $1$, perturbed by small white noise: $dy=f(y)\,dt+\sigma g(y)\,dW_t$. In local coordinates $(\theta,\rho)$ near $\mathcal O$, with phase $\theta$ and transversal deviation $\rho\in\mathbb R^{n-1}$, define the *stochastic Poincaré map* $\rho_n\mapsto\rho_{n+1}$ by successive returns of the phase to a section. To leading order it has the form

$$\bar\rho=A(I+\sigma B\zeta)\rho+\sigma\eta+O(\sigma^2,|\rho|^2),\qquad A=X(1),\ B=X^{-1}(1)\dot X(1),$$

where $X$ is the fundamental matrix of the linearized transversal dynamics, so the spectral radius of $A$ is less than $1$. Here $\zeta,\eta$ are explicit Gaussian Itô integrals over one period, $\zeta=\xi-b(1)^{\top}\eta$, so the noise is both additive and multiplicative. Let $D_h$ be the ball of radius $h$ about the fixed point $\rho=0$.

**Theorem.** Fix $h>0$. There are $\delta_0,\sigma_0=O(\epsilon)$ and constants $C_1,\dots,C_4>0$, independent of $\sigma$ and of the starting point, such that for every $y_0\in D_h$, $\sigma\in(0,\sigma_0)$ and $\delta\in(0,\delta_0)$ the number $\tau$ of iterations until the first exit from $D_h$ is asymptotically geometric with parameter

$$C_1\sigma e^{-C_2/\sigma^2}\big(1+O(\sigma^2)\big)\le p\le C_3\sigma e^{-C_4/\sigma^2}\big(1+O(\sigma^2)\big).$$

The return time per iteration satisfies $\tau_\sigma=1+b(1)^{\top}X(1)\rho_0-\sigma\zeta_1+o(\sigma)+O(|\rho_0|^2)$.

## Proof sketch

Away from the cycle the deterministic flow contracts, so an exit from $D_h$ needs a large deviation built up over many returns. Each return is close to a Gaussian autoregression $\rho_{n+1}\approx A\rho_n+\sigma\eta_n$, whose stationary law has covariance of order $\sigma^2$. The chance of leaving a ball of fixed radius in one step is therefore of order $e^{-c/\sigma^2}$, and successive attempts are almost independent, which makes the exit time asymptotically geometric. Nonlinear and multiplicative corrections change only the constants. In conductance-based neuron models the exit from a neighborhood of a stable limit cycle marks the switch between oscillatory regimes. This gives the statistics of irregular bursting and of mixed-mode oscillations: the number of small oscillations between spikes is geometrically distributed with an exponentially small parameter.

## Sources

- Pawel Hitczenko and Georgi S. Medvedev, "The Poincaré Map of Randomly Perturbed Periodic Motion", *Journal of Nonlinear Science* 23 (2013), 835–861, <https://doi.org/10.1007/s00332-013-9170-9>. Preprint version: arXiv:1206.0380 (2012), Lemma 2.3 (form of the first-return map), Theorem 2.6 (exit time for the linearized map), Lemma 3.2 (return time), Theorem 4.1 (asymptotically geometric exit time for the perturbed system), Section 6 (applications to bursting and mixed-mode oscillations in neuron models), <https://doi.org/10.48550/arXiv.1206.0380>.
