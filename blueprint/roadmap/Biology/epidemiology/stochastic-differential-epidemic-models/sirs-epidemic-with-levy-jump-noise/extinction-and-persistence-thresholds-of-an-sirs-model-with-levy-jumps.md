# Extinction and persistence thresholds of an SIRS model with Lévy jumps in the contact rate

**Model.** With recruitment $\theta > 0$, contact rate $\xi > 0$, natural death $\eta > 0$, recovery $\gamma > 0$ and loss of immunity $\rho \ge 0$, the deterministic model is

$$\dot S = \theta - \xi SI - \eta S + \rho R, \qquad \dot I = \xi SI - (\eta + \gamma)I, \qquad \dot R = \gamma I - (\eta + \rho)R,$$

with reproduction number $\psi_0 = \dfrac{\xi\theta}{\eta(\eta+\gamma)}$ and disease-free state $S = \theta/\eta$. Jump perturbations of the contact rate give

$$dS_t = (\theta - \xi S_tI_t - \eta S_t + \rho R_t)\,dt - \int_{\mathbb{Z}} \epsilon(u)\,S_{t^-}I_{t^-}\,\tilde N(dt,du),$$

$$dI_t = \big(\xi S_tI_t - (\eta+\gamma)I_t\big)\,dt + \int_{\mathbb{Z}} \epsilon(u)\,S_{t^-}I_{t^-}\,\tilde N(dt,du),$$

with $R$ as before, where $\tilde N$ is a compensated Poisson random measure with Lévy measure $\nu$ on a set $\mathbb{Z} \subset (0,\infty)$, and $\epsilon$ is bounded with $\epsilon(u) > -1$ and $\int_{\mathbb{Z}} \big(\ln(1+\epsilon(u))\big)^2\nu(du) < \infty$. Define

$$\varphi = \int_{\mathbb{Z}}\Big[\ln\Big(1 + \epsilon(u)\frac{\theta}{\eta}\Big) - \epsilon(u)\frac{\theta}{\eta}\Big]\nu(du), \qquad \psi = \psi_0 - \frac{\varphi}{\eta + \gamma}.$$

**Theorem.** Under the assumption on $\epsilon$:
1. For every initial value in $\mathbb{R}_+^2$ there is a unique global positive solution $(S_t, I_t)$.
2. *Extinction.* If $\psi < 1$, then almost surely

$$\limsup_{t\to\infty}\frac{\ln I_t}{t} \le (\eta + \gamma)(\psi - 1) < 0.$$

3. *Persistence in mean.* If $\psi > 1$, the time averages $\langle X\rangle_t = \frac1t\int_0^t X_s\,ds$ satisfy, almost surely,

$$\langle I\rangle_t \to (\eta+\gamma)(\psi - 1), \qquad \langle R\rangle_t \to \frac{\gamma(\eta+\gamma)}{\eta + \rho}(\psi - 1),$$

$$\langle S\rangle_t \to \frac{\theta}{\eta} - \frac{\eta + \gamma + \rho}{\eta + \rho}(\eta + \gamma)(\psi - 1).$$

For the deterministic model, the disease-free equilibrium is locally stable if $\psi_0 < 1$ and unstable if $\psi_0 > 1$, and a unique endemic equilibrium exists when $\psi_0 > 1$.

## Proof sketch

Apply Itô's formula for jump processes to $\ln I_t$: the jump term contributes the compensator correction $\int[\ln(1 + \epsilon S) - \epsilon S]\,\nu(du)$, which, evaluated at the disease-free level $S = \theta/\eta$, is $\varphi$. Bounding $S_t$ by its disease-free comparison process and using the strong law of large numbers for the martingale part gives the extinction rate $(\eta+\gamma)(\psi - 1)$. For persistence, integrating the equations and using the same martingale limits yields the time-average limits. The jump correction shifts the deterministic threshold $\psi_0$ to $\psi$, so jump noise can decide between extinction and persistence when $\psi_0$ is near $1$.

## Sources

- Daniel Desta, Almaz Abebe and James Brannan, "Dynamical systems framework for modeling COVID-19 with Lévy noise", *Stochastics and Dynamics* 26 (2026), 2550040, <https://doi.org/10.1142/s0219493725500406>. Preprint version: arXiv:2112.14876 (2021), Theorems 2 and 3 (Section 3), Assumption 1, Theorem 5, the definition of $\psi$ and Theorems 6 and 7 (Section 4), <https://doi.org/10.48550/arXiv.2112.14876>.
