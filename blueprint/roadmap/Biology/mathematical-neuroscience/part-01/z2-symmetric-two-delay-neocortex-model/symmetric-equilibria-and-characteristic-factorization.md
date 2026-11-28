# Symmetric equilibria and characteristic factorization of the two-delay neocortex model

Two identical cortical populations $x_1, x_2$ with delayed self-inhibition (delay $\tau_1$) and delayed mutual excitation (delay $\tau_2$) are modelled, after non-dimensionalization, by

$$\dot x_1(t) = -x_1(t) - \alpha_1 S\big(\beta_1 x_1(t - \tau_1)\big) + \alpha_2 S\big(\beta_2 x_2(t - \tau_2)\big),$$

$$\dot x_2(t) = -x_2(t) - \alpha_1 S\big(\beta_1 x_2(t - \tau_1)\big) + \alpha_2 S\big(\beta_2 x_1(t - \tau_2)\big),$$

with $\alpha_i, \beta_i, \tau_i > 0$ and $S$ smooth with $S' > 0$ (so strictly increasing), $S(0) = 0$, $S'(0) = 1$. The system is equivariant under the swap $\xi(x_1, x_2) = (x_2, x_1)$.

**Theorem (equilibria).** Every equilibrium is symmetric: $f(x^*) = 0$ implies $x^* = (x^*, x^*)$. The origin is always an equilibrium.

**Theorem (factorization).** At a symmetric equilibrium put $k_1 = \alpha_1\beta_1 S'(\beta_1 x^*) > 0$ and $k_2 = \alpha_2\beta_2 S'(\beta_2 x^*) > 0$. The characteristic equation of the linearization factors as

$$\det\Delta(\lambda) = \Delta_+(\lambda)\,\Delta_-(\lambda) = 0, \qquad \Delta_\pm(\lambda) = \lambda + 1 + k_1 e^{-\lambda\tau_1} \pm k_2 e^{-\lambda\tau_2}.$$

Roots of $\Delta_-$ have eigenvectors fixed by $\xi$ (in-phase modes); roots of $\Delta_+$ have eigenvectors with $\xi v = -v$ (anti-phase modes).

**Theorem (steady-state bifurcations).** The linearization has a zero eigenvalue if and only if $1 + k_1 + k_2 = 0$ or $1 + k_1 - k_2 = 0$. Since $k_1, k_2 > 0$, only the second (in-phase) condition can hold, so there are no symmetry-breaking steady-state bifurcations.

**Theorem (Hopf curves).** Purely imaginary roots $\pm i\omega$ lie, when $\sin(\omega(\tau_2 - \tau_1)) \ne 0$, on the curves

$$\begin{pmatrix}k_1\\k_2\end{pmatrix} = h_\pm(\omega) = \frac{-1}{\sin(\omega(\tau_2 - \tau_1))}\begin{pmatrix}\sin\omega\tau_2 & \cos\omega\tau_2\\ \mp\sin\omega\tau_1 & \mp\cos\omega\tau_1\end{pmatrix}\begin{pmatrix}1\\ \omega\end{pmatrix},$$

with $h_+$ for $\Delta_+$ and $h_-$ for $\Delta_-$, and otherwise on lines $k_1 + \sigma k_2 = -1/\cos(\omega\tau_1)$, $\sigma = \pm 1$, when $\omega = -\tan\omega\tau_1 = -\tan\omega\tau_2$. A Hopf bifurcation through $\Delta_-$ produces in-phase periodic solutions; a Hopf bifurcation through a simple root of $\Delta_+$ produces anti-phase periodic solutions with $x_1(t) = x_2(t + T/2)$, $T$ the period.

## Expansion

For equilibria define $H(x) = \beta_2^{-1} S^{-1}\big(\alpha_2^{-1}(x + \alpha_1 S(\beta_1 x))\big)$, which is strictly increasing; equilibria satisfy $x_2^* = H(x_1^*)$ and $x_1^* = H(x_2^*)$, and $x_1^* < x_2^*$ would give $x_2^* = H(x_1^*) < H(x_2^*) = x_1^*$, a contradiction. The characteristic matrix is circulant, $\begin{pmatrix} a & -b \\ -b & a\end{pmatrix}$ with $a = \lambda + 1 + k_1 e^{-\lambda\tau_1}$ and $b = k_2 e^{-\lambda\tau_2}$, so its eigenvectors are $(1, 1)$ and $(1, -1)$ with eigenvalues $a - b$ and $a + b$. The Hopf curves come from splitting $\Delta_\pm(i\omega) = 0$ into real and imaginary parts, a linear system in $(k_1, k_2)$. The anti-phase symmetry of the bifurcating orbit follows because the critical eigenvector satisfies $\xi p = -p$ and the equation commutes with $\xi$, so a half-period shift acts as the swap.

## Sources

- S. Visser, H. G. E. Meijer, M. J. A. M. van Putten, S. A. van Gils, Analysis of stability and bifurcations of fixed points and periodic solutions of a lumped model of neocortex with two delays, Journal of Mathematical Neuroscience 2 (2012), Section 2 (Theorems 1, 2, 5, 6 and 7). <https://doi.org/10.1186/2190-8567-2-8> PMCID: PMC3478171
