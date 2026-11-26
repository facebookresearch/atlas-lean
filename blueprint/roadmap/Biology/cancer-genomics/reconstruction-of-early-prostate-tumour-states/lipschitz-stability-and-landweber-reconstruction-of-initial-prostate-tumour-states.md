# Lipschitz stability and Landweber reconstruction of initial prostate tumour states

**Model.** On a bounded $C^2$ domain $\Omega \subset \mathbb{R}^N$, $N = 2,3$, a prostate tumour is described by a phase field $\phi$ ($\phi \approx 1$ tumour, $\phi \approx 0$ healthy tissue), a nutrient $\sigma$ and tissue prostate-specific antigen (PSA) $p$:

$$\begin{aligned}
\partial_t\phi &= \lambda\Delta\phi - F'(\phi) + m(\sigma)h'(\phi),\\
\partial_t\sigma &= \eta\Delta\sigma + S_h(1-\phi) + S_c\phi - \big(\gamma_h(1-\phi) + \gamma_c\phi\big)\sigma,\\
\partial_t p &= D\Delta p + \alpha_h(1-\phi) + \alpha_c\phi - \gamma_p p,
\end{aligned}$$

with $\phi = 0$, $\partial_n\sigma = \partial_n p = 0$ on $\partial\Omega$, double well $F(\phi) = M\phi^2(1-\phi)^2$, interpolation $h(\phi) = M\phi^2(3-2\phi)$, and nutrient-dependent net proliferation $m(\sigma) = m_{ref}\big(\frac{\rho+A}{2} + \frac{\rho-A}{\pi}\arctan\frac{\sigma-\sigma_l}{\sigma_r}\big)$. Serum PSA is $P_s = \int_\Omega p\,dx$. The **inverse problem** is to recover the initial state $\psi_0 = (\phi_0,\sigma_0,p_0)$ from a single measurement of $\mathcal{R}(\psi_0) = (\phi,\sigma,p)(T)$ at a later time $T$.

**Theorem.**

*(1)* (Conditional logarithmic stability) For two admissible initial data, if $\varepsilon$, the $H$-distance of the two final states divided by an a priori bound $M$, is small enough, then the initial data differ by at most a constant times a logarithmic modulus of $\varepsilon$.

*(2)* (Lipschitz stability on finite-dimensional sets) If the admissible initial data lie in a compact subset $K$ of a finite-dimensional subspace $\Lambda$, there is an explicit $C_s$ with

$$\|\psi^1_0 - \psi^2_0\|_{H} \le C_s\,\|\mathcal{R}(\psi^1_0) - \mathcal{R}(\psi^2_0)\|_{H}.$$

*(3)* (Landweber convergence) Suppose $\mathcal{R}(\bar\psi_0) = \psi_{meas}$ for some $\bar\psi_0 \in K$. For the Landweber iteration $\psi^{j+1}_0 = \psi^j_0 - \mu\,\mathcal{R}'(\psi^j_0)^*\big[\vec\kappa\cdot(\mathcal{R}(\psi^j_0) - \psi_{meas})\big]$, with weights $\vec\kappa = (\kappa_1,\kappa_2,\kappa_3)$ on the three components and the adjoint of the Fréchet derivative computed through a backward adjoint system, there are $\rho > 0$, $0 < c < 1$ and $\mu^* > 0$ such that $\|\psi^0_0 - \bar\psi_0\|^2_H \le \rho$ and $\mu|\vec\kappa| < \mu^*$ imply

$$\|\psi^j_0 - \bar\psi_0\|^2_H \le \rho(1-c)^j \quad\text{for all } j,$$

so the iterates converge linearly to the true initial tumour state.

## Expansion

Backward reconstruction for a parabolic system is severely ill posed in general; Lipschitz stability is recovered by restricting the unknown to a finite-dimensional compact set, where it follows from the logarithmic estimate and a quantitative injectivity of the linearized forward map. The forward map is Fréchet differentiable with Lipschitz derivative, and the Fréchet derivative's adjoint is computed by solving a backward linear adjoint system driven by the weighted final-time misfit. Lipschitz stability of the inverse plus a Lipschitz derivative are exactly the hypotheses of a local linear-convergence result for Landweber iteration, which gives the rate $(1-c)^j$; an adaptive step size speeds up the reconstruction in simulations with isogeometric discretization and noisy data.

## Sources

- Elena Beretta, Cecilia Cavaterra, Matteo Fornoni, Guillermo Lorenzo and Elisabetta Rocca, "Iterative algorithms for the reconstruction of early states of prostate cancer growth", arXiv:2409.12844 (2024), Section 2, Section 3 (Theorems 3.1 and 3.2) and Section 4 (Proposition 4.2, Theorem 4.5), <https://doi.org/10.48550/arXiv.2409.12844>.
