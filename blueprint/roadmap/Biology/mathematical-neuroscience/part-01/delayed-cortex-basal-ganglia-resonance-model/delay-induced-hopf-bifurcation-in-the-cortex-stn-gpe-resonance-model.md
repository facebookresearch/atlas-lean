# Delay-induced Hopf bifurcation in the cortex-STN-GPe resonance model

Let $S, G, E, I$ be the firing rates of the subthalamic nucleus (STN), the external globus pallidus (GPe), and the excitatory and inhibitory cortical populations. With a common membrane time constant $\tau > 0$ and a common synaptic transmission delay $T \ge 0$, the resonance model is

$$\tau S'(t) = F_S\big(w_{CS} E(t-T) - w_{GS} G(t-T)\big) - S(t),$$

$$\tau G'(t) = F_G\big(w_{SG} S(t-T) - w_{GG} G(t-T) - Str\big) - G(t),$$

$$\tau E'(t) = F_E\big(-w_{CC} I(t-T) + C\big) - E(t),$$

$$\tau I'(t) = F_I\big(w_{CC} E(t-T)\big) - I(t),$$

with positive weights $w_{ij}$, constant striatal inhibition $Str$, constant cortical drive $C$, and sigmoids $F_X(x) = M_X / \big(1 + \tfrac{M_X - B_X}{B_X} e^{-4x/M_X}\big)$ for $X \in \{S, G, E, I\}$, where $0 < B_X < M_X$.

Let $(S^*, G^*, E^*, I^*)$ be an equilibrium and put $\kappa_X = \tfrac{4}{M_X} X^* (1 - X^*/M_X) > 0$, which is $F_X'$ evaluated at the equilibrium input. Set

$$a_{12} = -\tfrac{w_{GS}\kappa_S}{\tau},\quad a_{13} = \tfrac{w_{CS}\kappa_S}{\tau},\quad a_{21} = \tfrac{w_{SG}\kappa_G}{\tau},\quad a_{22} = -\tfrac{w_{GG}\kappa_G}{\tau},\quad a_{34} = -\tfrac{w_{CC}\kappa_E}{\tau},\quad a_{43} = \tfrac{w_{CC}\kappa_I}{\tau}.$$

**Factorization.** The linearization $u' = -\tau^{-1} u(t) + B_2 u(t-T)$ has characteristic function $\Delta(\lambda) = \Delta_1(\lambda)\Delta_2(\lambda)$ with

$$\Delta_1(\lambda) = (\lambda + 1/\tau)^2 - (\lambda + 1/\tau) a_{22} e^{-\lambda T} - a_{12} a_{21} e^{-2\lambda T},$$

$$\Delta_2(\lambda) = (\lambda + 1/\tau)^2 - a_{34} a_{43} e^{-2\lambda T}.$$

$\Delta_1$ is the STN-GPe loop and $\Delta_2$ the cortical excitatory-inhibitory loop; the cortex-to-STN term $a_{13}$ does not enter the spectrum, because the cortex drives the basal ganglia without feedback in this model.

**Critical delays.** A root $\lambda = i\omega$, $\omega > 0$, of $\Delta_2$ requires $\omega^2 = -a_{34}a_{43} - 1/\tau^2 > 0$, and then occurs at the delays $T_5^j = \tfrac{1}{2\omega}\arccos\!\big(\tfrac{1/\tau^2 - \omega^2}{a_{34} a_{43}}\big) + \tfrac{j\pi}{\omega}$ (which agrees with the source's principal-arcsine form $-\tfrac{1}{2\omega}\arcsin\!\big(\tfrac{2\omega}{\tau a_{34} a_{43}}\big) + \tfrac{j\pi}{\omega}$ when $-a_{34}a_{43} \ge 2/\tau^2$), $j = 0, 1, 2, \dots$. A root $i\omega$ of $\Delta_1$ requires $z = \omega^2$ to be a positive root of a quartic $z^4 + k_1 z^3 + k_2 z^2 + k_3 z + k_4 = 0$ whose coefficients are explicit polynomials in $1/\tau$, $a_{22}$ and $a_{12}a_{21}$ (source Eqs. 13 to 15), and each such root gives a sequence of critical delays $T_k^j$ (source Eq. 16). Let $T_0$ be the smallest critical delay and $\pm i\omega_0$ the corresponding roots.

**Hopf theorem.** Assume (H1) the quartic has a positive root, (H2) the transversality condition $\operatorname{Re}\,(d\lambda/dT)^{-1}\big|_{\lambda = i\omega_0} \ne 0$ holds, and (H3) at $T = 0$ the quartic $\lambda^4 + d_3\lambda^3 + d_2\lambda^2 + d_1\lambda + d_0$ obtained from $\Delta$ satisfies the Routh-Hurwitz conditions $d_i > 0$, $d_3 d_2 > d_1$, $d_3 d_2 d_1 > d_1^2 + d_3^2 d_0$. Then the equilibrium is asymptotically stable for $0 \le T < T_0$ and the system undergoes a Hopf bifurcation at $T = T_0$. Writing $c_1(0)$ for the first coefficient of the Poincare normal form on the two-dimensional center manifold, $\mu_2 = -\operatorname{Re} c_1(0) / \operatorname{Re}\lambda'(T_0)$ fixes the direction (supercritical if $\mu_2 > 0$), $\beta_2 = 2\operatorname{Re} c_1(0)$ fixes the stability of the periodic orbit (stable if $\beta_2 < 0$), and the period is $\tfrac{2\pi}{\omega_0}(1 + T_2\varepsilon^2 + O(\varepsilon^3))$.

## Expansion

Because every delayed coupling uses the same lag $T$, the Jacobian splits into a $2 \times 2$ STN-GPe block, a $2 \times 2$ cortical block and an off-diagonal cortex-to-STN entry that sits above the block diagonal, so the determinant is the product of the two loop determinants. Setting $\lambda = i\omega$ and separating real and imaginary parts gives $\sin\omega T$ and $\cos\omega T$ explicitly; eliminating $T$ through $\sin^2 + \cos^2 = 1$ gives the frequency equation. The exponential-polynomial root-counting lemma (zeros can enter the right half plane only across the imaginary axis) together with (H3) at $T = 0$ shows stability up to the first crossing, the same crossing argument as for the [delayed logistic equation](../../../population-dynamics/hopf-bifurcation-of-the-delayed-logistic-equatio/README.md); the model itself is a delayed rate model of [Wilson–Cowan](../../wilson-cowan-neural-population-model/README.md) type. With parameter values fitted to rat recordings (weights $w_{SG} = 2.56$, $w_{GS} = 3.22$, $w_{CC} = 2.75$, $w_{CS} = 6.60$, $w_{GG} = 0.90$, $C = 277.94$, $Str = 40.51$, $\tau = 10$ ms), the source reports $T_0 = 3.6807$ ms with $\mu_2 = 5.5252 \times 10^{-4} > 0$ and $\beta_2 = -1.4874 \times 10^{-5} < 0$: a supercritical Hopf bifurcation to a stable beta-band oscillation, which appears first in the excitatory cortical population and is followed at the same frequency by the basal ganglia.

## Sources

- Y. Chen, J. Wang, Y. Kang, M. B. Ghori, Emergence of beta oscillations of a resonance model for Parkinson's disease (2020), Sections 2.1 and 2.2 and Section 3.1. <https://doi.org/10.1155/2020/8824760> PMCID: PMC7722408
