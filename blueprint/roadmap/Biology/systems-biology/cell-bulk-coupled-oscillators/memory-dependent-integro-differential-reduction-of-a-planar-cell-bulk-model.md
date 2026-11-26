# Memory-dependent integro-differential reduction of a planar cell-bulk model

**Model.** $N$ small cells $\Omega_{\varepsilon_j}=\{|x-x_j|\le\varepsilon\}$, well separated in $\mathbb R^2$, exchange a signalling molecule with a bulk diffusion field $U(x,t)$:

$$\partial_tU=D\Delta U-\sigma U\quad\text{in }\mathbb R^2\setminus\textstyle\bigcup_j\Omega_{\varepsilon_j},\qquad U(x,0)=0,\qquad \varepsilon D\,\partial_nU=d_{1j}U-d_{2j}u_{1j}\ \text{on }\partial\Omega_{\varepsilon_j},$$

coupled to intracellular kinetics $\mathbf u_j\in\mathbb R^m$,

$$\frac{d\mathbf u_j}{dt}=\mathbf F_j(\mathbf u_j)+\frac{\mathbf e_1}{\varepsilon}\int_{\partial\Omega_{\varepsilon_j}}\bigl(d_{1j}U-d_{2j}u_{1j}\bigr)\,dS,$$

so that only the first intracellular species is secreted and absorbed with permeabilities $d_{2j}$ (efflux) and $d_{1j}$ (influx). Let $\nu=-1/\log\varepsilon$, $E_1$ the exponential integral and $\gamma_e$ Euler's constant.

**Reduced system.** As $\varepsilon\to0$, for $t\gg O(\varepsilon^2)$ the model is approximated by

$$\frac{d\mathbf u_j}{dt}=\mathbf F_j(\mathbf u_j)+\mathbf e_1B_j(t),$$

$$\int_0^tB_j'(\tau)E_1\bigl(\sigma(t-\tau)\bigr)d\tau=\eta_jB_j(t)+\gamma_ju_{1j}(t)+\sum_{k\ne j}\int_0^t\frac{B_k(\tau)e^{-\sigma(t-\tau)}}{t-\tau}e^{-|x_j-x_k|^2/(4D(t-\tau))}d\tau,$$

with $\eta_j=2\bigl(\frac1\nu+\frac D{d_{1j}}+\log(2\sqrt{D/\sigma})-\gamma_e\bigr)$ and $\gamma_j=4\pi Dd_{2j}/d_{1j}$. The bulk field is $U(x,t)\sim-\frac1{4\pi D}\sum_j\int_0^t\frac{B_j(\tau)e^{-\sigma(t-\tau)}}{t-\tau}e^{-|x-x_j|^2/(4D(t-\tau))}d\tau$, a superposition of heat-kernel sources of strength $B_j$.

**Steady states and stability.** Bounded limits $B_j\to B_{j\infty}$, $\mathbf u_j\to\mathbf u_{j\infty}$ satisfy an $N(m+1)$-dimensional nonlinear algebraic system with the modified Bessel Green's matrix. The discrete eigenvalues of the linearization are the roots of $\det\mathcal M(\lambda)=0$, where

$$\mathcal M(\lambda)=I+2\pi\nu\,\mathcal G_\lambda+\nu D\,P_1+2\pi\nu D\,P_2\,\mathcal K(\lambda),$$

$P_1=\mathrm{diag}(1/d_{1j})$, $P_2=\mathrm{diag}(d_{2j}/d_{1j})$, $\mathcal K(\lambda)=\mathrm{diag}\bigl(\mathbf e_1^\top(\lambda I-J_j)^{-1}\mathbf e_1\bigr)$ with $J_j$ the intracellular Jacobians, and $\mathcal G_\lambda$ is the eigenvalue-dependent reduced-wave Green's matrix of the cell configuration.

## Expansion

In two dimensions a small cell is seen by the bulk as a point source with a logarithmic inner correction, which is why $\nu=-1/\log\varepsilon$ appears (strong localized perturbation theory). Matching the time-dependent inner and outer solutions turns the bulk PDE into the history-dependent (memory) integral equations for the source strengths $B_j$. Hopf bifurcations of $\det\mathcal M(\lambda)=0$ predict when diffusive coupling triggers synchronized or phase-locked intracellular oscillations (e.g. Sel'kov kinetics); the memory integrals are evaluated fast with a sum-of-exponentials approximation.

## Sources

- Merlin Pelz and Michael J. Ward, "Synchronized Memory-Dependent Intracellular Oscillations for a Cell-Bulk ODE-PDE Model in $\mathbb{R}^2$", arXiv:2409.00623 (2024), Section 2 (dimensionless cell-bulk model), Section 3 (Proposition 1) and Section 4 (Propositions 2–3), <https://doi.org/10.48550/arXiv.2409.00623>.
