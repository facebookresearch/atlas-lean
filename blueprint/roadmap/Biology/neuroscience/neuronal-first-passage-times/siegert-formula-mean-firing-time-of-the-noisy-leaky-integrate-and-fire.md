# Siegert formula for the mean firing time of the noisy leaky integrate-and-fire neuron

Let the subthreshold membrane potential of a leaky integrate-and-fire neuron be the Ornstein–Uhlenbeck process $dX(t) = (\mu - \kappa X(t))\, dt + \sigma\, dW(t)$ with $\kappa, \sigma > 0$, started after each spike at the reset value $y < \theta$, where $\theta$ is the firing threshold. The mean first-passage time from $y$ to $\theta$ is
$$m_1(\theta, y) = \frac{\sqrt\pi}{\kappa} \int_{(\kappa y - \mu)/(\sigma\sqrt\kappa)}^{(\kappa\theta - \mu)/(\sigma\sqrt\kappa)} e^{z^2} \bigl(1 + \operatorname{erf} z\bigr)\, dz,$$
and with an absolute refractory period $T_r \ge 0$ after each spike the mean time to fire is $T_r + m_1(\theta, y)$ and the average firing rate is $\rho = 1/(T_r + m_1(\theta, y))$. This is the first-moment case of Siegert's formula (1951); Kreutz-Delgado (2015) derives it from the general Siegert recursion for the moments of the first-passage time (equation (51) there, with the model in equation (9)).


## Expansion

1. The model: the Ornstein–Uhlenbeck process (with [its Itô solution](../../../Probability/stochastic-calculus/it-integral/ae-tendsto-ou-ito-integral-riemann.md)), the threshold, the reset and the refractory period, and the renewal spike train.
2. The mean first-passage time of a one-dimensional diffusion to an upper level as the solution of the backward equation $L m_1 = -1$ with the boundary conditions at the threshold and at $-\infty$, written with the scale density.
3. The computation for the standardized process, whose scale density is $e^{x^2}$, and the identity $\int_{-\infty}^y e^{-z^2} dz = \frac{\sqrt\pi}{2}(1 + \operatorname{erf} y)$, giving the formula.
4. The firing rate as the reciprocal of the mean time to fire, as an elementary renewal statement.
5. The higher moments of the first-passage time from the general Siegert recursion, as separate statements.

## Sources

- A. J. F. Siegert, On the first passage time probability problem, Phys. Rev. 81 (1951), 617–623. <https://doi.org/10.1103/PhysRev.81.617>
- K. Kreutz-Delgado, Mean time-to-fire for the noisy LIF neuron: a detailed derivation of the Siegert formula, 2015, equations (9) and (51). <https://arxiv.org/abs/1501.04032>
