# 3D-1D Darcy–Poiseuille perfusion model and its slender-body 1D limit

**Geometry.** Tissue perfused by a dense capillary bed is a porous medium filling the half-space $\mathbb{R}^3_+$. A thin blood vessel enters through the wall $z = 0$: its centerline is a non-self-intersecting unit-length $C^2$ curve $\mathbf{X}(s)$, $s \in [0,1]$, perpendicular to the wall at $s = 0$, with circular cross sections of radius $\epsilon a(s)$, $0 < \epsilon \ll 1$. The radius profile $a \in C^2[0,1)$ satisfies $\|a\|_\infty = 1$, $a \ge a_0 > 0$ away from the tip, $\sup|aa'| < \infty$, $\sup|a^3a''| < \infty$, and is spheroidal at the free end, $|a(s) - \sqrt{1-s^2}| \le C\epsilon^2\sqrt{1-s^2}$. Let $\Gamma_\epsilon$ be the vessel surface, $\Omega_\epsilon = \mathbb{R}^3_+ \setminus \overline{\mathcal{V}_\epsilon}$ the tissue, and $\mathcal{J}_\epsilon$ the surface Jacobian.

**3D-1D Darcy–Poiseuille model.** The tissue pressure $q$ and the vessel (blood) pressure $p(s)$ solve

$$
\begin{aligned}
\Delta q &= 0 && \text{in } \Omega_\epsilon,\\
\partial_{\mathbf n} q &= \tfrac{\omega}{\epsilon}\big(p(s) - q\big) && \text{on } \Gamma_\epsilon \quad (\text{membrane leakage, Robin}),\\
\textstyle\int_0^{2\pi}\partial_{\mathbf n}q\,\mathcal{J}_\epsilon(s,\theta)\,d\theta &= \eta\,\tfrac{d}{ds}\big(a^4(s)\tfrac{dp}{ds}\big) && \text{on } \Gamma_\epsilon \quad (\text{Poiseuille mass balance}),\\
\partial_{\mathbf n} q &= 0 \ \text{on } \partial\Omega_\epsilon\setminus\Gamma_\epsilon, \quad q \to 0 \text{ as } |\mathbf{x}| \to \infty, && p(0) = p_0 .
\end{aligned}
$$

**1D slender-body model.** With $\mathcal{G}_N$ the Neumann Green's function of the half-space and $\mathcal{S}_N[f]\,(\mathbf{x}) = \int_0^1\mathcal{G}_N(\mathbf{x},\mathbf{X}(\varphi_\epsilon^{-1}(t)))f(t)\,dt$ (a line source along an effective centerline stretched by $\varphi_\epsilon$), set $q^{\mathrm{SB}} = \eta\,\mathcal{S}_N\big[(a^4p^{\mathrm{SB}}_s)_s\big]$, where $p^{\mathrm{SB}}$, $p^{\mathrm{SB}}(0) = p_0$, solves the integrodifferential equation

$$ -\eta\big(a^4p^{\mathrm{SB}}_s\big)_s + 2\pi a(s)\,\omega\,p^{\mathrm{SB}} = a(s)\,\omega\,\eta\int_0^{2\pi}\mathcal{S}_N\big[(a^4p^{\mathrm{SB}}_s)_s\big]\Big|_{\Gamma_\epsilon}\,d\theta . $$

**Theorem.** With $D^{1,2}(\Omega_\epsilon) = L^6 \cap \dot H^1$ and $\mathcal{H}^a(0,1)$ the $a^4$-weighted energy space:
1. (Well-posedness) The 3D-1D system has a unique solution $(q,p)$ with $\|q\|_{D^{1,2}} + |\Gamma_\epsilon|^{-1/2}\|p - q\|_{L^2(\Gamma_\epsilon)} + \|p\|_{\mathcal{H}^a} \le C|p_0|$, $C$ independent of $\epsilon$.
2. (1D estimates) For $\epsilon$ small, the 1D equation has a unique solution with $\|p^{\mathrm{SB}}\|_{\mathcal{H}^a} \le C|p_0|$, $\|p^{\mathrm{SB}}\|_{L^\infty} + \|a\,p^{\mathrm{SB}}_s\|_{L^\infty} \le C\epsilon^{-1/2}|p_0|$, and weighted bounds on higher derivatives that lose at most a factor $|\log\epsilon|$.
3. (Convergence) 

$$ \|q^{\mathrm{SB}} - q\|_{D^{1,2}(\Omega_\epsilon)} + \epsilon^{-1/2}\big\|(p^{\mathrm{SB}} - p) - (q^{\mathrm{SB}} - q)\big\|_{L^2(\Gamma_\epsilon)} + \|p^{\mathrm{SB}} - p\|_{\mathcal{H}^a(0,1)} \le C\,\epsilon^{1/2}|\log\epsilon|\,|p_0| . $$

The Green's-function vessel models used in microcirculation are therefore a rigorous thin-vessel limit of the 3D-1D coupling.

## Expansion

Well-posedness follows from Lax–Milgram: the energy pairs the Dirichlet energy of $q$, the leakage term $\frac{\omega}{\epsilon}\int_{\Gamma_\epsilon}|p - q|^2$, and the Poiseuille energy $\eta\int a^4|p_s|^2$, and the angle-averaged Neumann condition makes them compatible. The 1D equation is the analogue of slender-body theory with an unknown line density $(a^4p_s)_s$; its integral operator is nearly positive and its kernel derivatives nearly antisymmetric, which gives coercivity uniform in $\epsilon$. The convergence rate comes from the residual of $q^{\mathrm{SB}}$ in the Robin and Neumann conditions on $\Gamma_\epsilon$, which is $O(\epsilon^{1/2}|\log\epsilon|)$, fed through the 3D-1D stability estimate.

## Sources

- Laurel Ohm and Sarah Strikwerda, "A hierarchy of blood vessel models, Part I: 3D-1D to 1D", arXiv:2507.13316 (2025), Section 1, Theorems 1.1, 1.2 and 1.3; Sections 3–5 and Appendix A, <https://doi.org/10.48550/arXiv.2507.13316>.
