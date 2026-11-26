# Well-posedness of the time-fractional mechanically coupled tumour growth model

**Model.** On a bounded Lipschitz domain $\Omega\subset\mathbb R^d$ over $(0,T)$, let $\phi$ be the tumour volume fraction, $\mu$ its chemical potential, $\vec u$ the displacement, $\psi$ the nutrient and $\chi$ the chemotherapeutic agent. Subdiffusion of tumour cells is modeled by a fractional order $\alpha\in(0,1)$ in time:

$$
\begin{aligned}
\partial_t^{\alpha}(\phi-\phi_0)&=\nabla\cdot\big(M_\phi(x)\nabla\mu\big)+N_\phi f(\phi,\psi)-P_\phi g(\phi,\chi),\\
\mu&=c\,\phi+\lambda\,\nabla\cdot\vec u,\\
\vec 0&=\nabla\cdot\Big(2G\,\varepsilon(\vec u)+\tfrac{2G\nu}{1-2\nu}\operatorname{tr}\varepsilon(\vec u)\,\mathbb I+\lambda\phi\,\mathbb I\Big),\\
\partial_t\psi&=\nabla\cdot\big(M_\psi\nabla\psi\big)+S_\psi-N_\psi f(\phi,\psi),\\
\partial_t\chi&=\nabla\cdot\big(M_\chi\nabla\chi\big)-N_\chi\chi+S_\chi-P_\chi g(\phi,\chi),
\end{aligned}
$$

where $\partial_t^{\alpha}(\phi-\phi_0)=\partial_t\big(g_{1-\alpha}*(\phi-\phi_0)\big)$ with $g_{\beta}(t)=t^{\beta-1}/\Gamma(\beta)$ (a Caputo derivative written through the Riemann–Liouville form, which needs less regularity), $\varepsilon(\vec u)$ is the symmetric gradient, $G>0$ the shear modulus, $\nu<1/2$ the Poisson ratio, and typical uptake terms are $f=\phi(1-\phi)\psi/(K_\psi+\psi)$, $g=\phi(1-\phi)\chi/(K_\chi+\chi)$. Boundary data: no flux for $\mu$; $\vec u=0$ on a part $\Gamma_u$ of positive measure and traction-free elsewhere; Dirichlet data for $\psi,\chi$ on a part $\Gamma_\psi$ of positive measure and Neumann fluxes $\psi_b,\chi_b$ elsewhere.

**Theorem.** Assume

- (A1) $\phi_0,\psi_0,\chi_0\in L^2(\Omega)$ and $\psi_b,\chi_b\in L^2(0,T;L^2(\partial\Omega\setminus\Gamma_\psi))$;
- (A2) $f,g\in C_b(\mathbb R^2)$ with $0\le f\le C_f$, $0\le g\le C_g$;
- (A3) the mobilities $M_\phi,M_\psi,M_\chi$ are continuous with $0<M_0\le M\le M_\infty$;
- (A4) $S_\psi,S_\chi\in L^2(0,T;L^2(\Omega))$;
- (A5) $c>\lambda^2(1-2\nu)/(2G\nu)$.

Then there is a weak solution with $\phi$ in the fractional Sobolev-in-time class $W^{\alpha}_{2,2}(0,T;\phi_0,L^2,L^2)$, $\mu\in L^2(0,T;H^1)$, $\vec u\in L^2(0,T;H^1_{0,\Gamma_u})$ and $\psi,\chi\in L^2(0,T;H^1_{0,\Gamma_\psi})\cap H^1(0,T;H^{-1})$, satisfying

$$\|\phi\|^2_{L^2L^2}+\|\mu\|^2_{L^2H^1}+\|\vec u\|^2_{L^2H^1}+\|\psi\|^2_{L^2H^1}+\|\chi\|^2_{L^2H^1}\le C\big(\mathrm{IC}+C_f+C_g+\|S_\psi\|^2+\|S_\chi\|^2+\|\psi_b\|^2+\|\chi_b\|^2\big),$$

with $\mathrm{IC}=\|\phi_0\|^2+\|\psi_0\|^2+\|\chi_0\|^2$. If moreover $f$ and $g$ are Lipschitz, the weak solution is unique.

## Expansion

Formally taking the divergence of the elasticity equation (for constant $M_\phi$) eliminates $\vec u$ and gives $\partial_t^\alpha(\phi-\phi_0)=M_\phi\big(c-\tfrac{\lambda^2(1-2\nu)}{2G(1-\nu)}\big)\Delta\phi+\dots$, so some lower bound on $c$ is needed for a parabolic-type equation; (A5) is the slightly stronger condition the energy method uses. The proof is a Faedo–Galerkin scheme: the semi-discrete system is a multi-order system of fractional ODEs, solved by an integral reformulation and the Banach fixed-point theorem. Energy estimates use a fractional chain-rule inequality: for convex $F$, $\big(F'(\varphi),\partial_t(g_{1-\alpha}*\varphi)\big)\ge\partial_t\big(g_{1-\alpha}*\int_\Omega F(\varphi)\big)+\big(-\int_\Omega F(\varphi)+(F'(\varphi),\varphi)\big)g_{1-\alpha}(t)$, applied with the convex stored elastic energy, together with generalized Gronwall inequalities. Banach–Alaoglu and compactness theorems pass to the limit; uniqueness follows by testing the difference of two solutions under Lipschitz uptake terms.

The statement is the well-posedness theorem of the section on mathematical analysis of the source.

## Sources

- M. Fritz, C. Kuttler, M. L. Rajendran, B. Wohlmuth, L. Scarabosio, *On a subdiffusive tumour growth model with fractional time derivative*, arXiv:2006.10670 (2020). <https://doi.org/10.48550/arXiv.2006.10670>
