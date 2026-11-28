# Level invariance and spike map of the adaptive-threshold model

Let $I(t)$ be a continuous input and let the threshold $\theta(t)$ obey, in units of its time constant,

$$\frac{d\theta}{dt} = a\,I(t) - \theta(t), \qquad a \ge 0,$$

with a spike at each time $s$ where $\theta(s) = I(s)$, after which the threshold is multiplied by $\rho > 1$ ($\theta \mapsto \rho\theta$). Define the spike map $\varphi(t)$ as the first time $s > t$ with $\theta(s) = I(s)$, given $\theta(t) = \rho I(t)$.

1. (Level invariance) The dynamics are homogeneous of degree one in $(I, \theta)$, so replacing $I$ by $\lambda I$ for any $\lambda > 0$ leaves the spike map, and hence the spike times, unchanged.
2. For $a = 0$, two successive spikes satisfy $\rho\,I(t)\,e^{t - \varphi(t)} = I(\varphi(t))$, i.e. $\log\rho + \log I(t) + t = \log I(\varphi(t)) + \varphi(t)$; the restriction of $\varphi$ to its range is topologically conjugate to the translation $t \mapsto t + \log\rho$, so spike timing is neutrally stable and sensitive to initial conditions and noise.
3. After a step change of level from $I_1$ to $I_2$ (time constant $\tau_\theta$ restored), a decrease produces a silent period of about $\tau_\theta\log(I_1/I_2)$ and an increase produces a burst of about $\log(I_2/I_1)/\log\rho$ spikes, both proportional to the level change in decibels.

## Expansion

If $(\theta, I)$ is a solution with spikes at given times, so is $(\lambda\theta, \lambda I)$, since the ODE is linear, the spike condition $\theta = I$ is homogeneous and the reset is multiplicative. For $a = 0$ the threshold decays as $\rho I(t)e^{-(s-t)}$ after a spike, which gives the identity; with $\psi(t) = \log I(t) + t$ it reads $\psi\circ\varphi = T\circ\psi$ for $T(t) = t + \log\rho$, and one checks that $\psi$ is a homeomorphism on the range of $\varphi$. After a level drop the threshold must relax by the factor $I_2/I_1$, taking time $\tau_\theta\log(I_1/I_2)$; after a rise it must climb by $I_2/I_1$ in jumps of $\rho$. If $a \ge 1$ the response to constant currents is phasic, as for bushy cells of the cochlear nucleus.

## Sources

- R. Brette, "Spiking models for level-invariant encoding", Frontiers in Computational Neuroscience 5 (2012) 63, <https://doi.org/10.3389/fncom.2011.00063>, PMCID PMC3254166. Appendix A (A.1–A.2) and Appendix B, Theorem 1.
