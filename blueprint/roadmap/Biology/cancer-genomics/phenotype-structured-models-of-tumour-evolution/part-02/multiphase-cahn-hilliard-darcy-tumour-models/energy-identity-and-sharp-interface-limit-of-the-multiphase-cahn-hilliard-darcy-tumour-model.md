# Energy identity and sharp-interface limit of the multiphase Cahn–Hilliard–Darcy tumour model

**Model.** A tissue is a mixture of $L$ cell phases (for example host, proliferating, quiescent and necrotic tumour cells) with volume fractions $\bm\varphi=(\varphi_1,\dots,\varphi_L)$ in the Gibbs simplex ($\sum_i\varphi_i=1$). It contains $M$ chemical species $\bm\sigma$ (nutrient, angiogenic factors, toxins). Let $\mathbb P$ be the projection onto the tangent space $\{\sum_i\xi_i=0\}$ of the simplex. Using a volume-averaged mixture velocity $\vec v$, mass balance with a Darcy law and a Ginzburg–Landau free energy

$$\mathcal E(\bm\varphi,\bm\sigma)=\int_\Omega A\,\Psi(\bm\varphi)+B\,a(\bm\varphi,\nabla\bm\varphi)+N(\bm\varphi,\bm\sigma)\,dx$$

give the system

$$\begin{aligned}
\operatorname{div}\vec v&=\mathbf 1\cdot\bm U(\bm\varphi,\bm\sigma), \qquad \vec v=-K\nabla p+K(\nabla\bm\varphi)^\top\big(\bm\mu-N_{,\bm\varphi}\big),\\
\partial_t\bm\varphi+\operatorname{div}(\bm\varphi\otimes\vec v)&=\operatorname{div}\big(\mathbb C\,\nabla(\mathbb P\bm\mu)\big)+\bm U, \\
\bm\mu&=B\,a_{,\bm\varphi}-B\operatorname{div}a_{,\nabla\bm\varphi}+A\,\Psi_{,\bm\varphi}+N_{,\bm\varphi},\\
\partial_t\bm\sigma+\operatorname{div}(\bm\sigma\otimes\vec v)&=\operatorname{div}\big(\mathbb D\,\nabla N_{,\bm\sigma}\big)+\bm S .
\end{aligned}$$

Here $\Psi$ is a multi-well potential with minima at the pure phases, $a$ is a gradient energy, $N$ is the chemical free energy, $\mathbb C$ and $\mathbb D$ are mobility tensors, and $\bm U$ and $\bm S$ are mass-exchange terms: proliferation, apoptosis, necrosis, nutrient consumption.

**Theorem (energy identity).** Smooth solutions satisfy

$$\frac{d}{dt}\mathcal E=-\int_\Omega\Big(\mathbb C\nabla(\mathbb P\bm\mu):\nabla(\mathbb P\bm\mu)+\mathbb D\nabla N_{,\bm\sigma}:\nabla N_{,\bm\sigma}+\frac{|\vec v|^2}{K}\Big)dx-\int_\Omega\big(\bm S\cdot N_{,\bm\sigma}-\bm U\cdot\mathbb P\bm\mu\big)\,dx-\int_\Omega(\mathbf 1\cdot\bm U)\big(\bm\varphi\cdot\mathbb P\bm\mu+\bm\sigma\cdot N_{,\bm\sigma}-N-p\big)\,dx+(\text{boundary terms}).$$

Hence, with no-flux boundary conditions and no source terms ($\bm U=\bm S=0$), the free energy is non-increasing, which makes the model thermodynamically consistent.

**Formal sharp-interface limit.** The following is a formal derivation by matched asymptotic expansions in the source, not a proved convergence result. Take $A=\beta/\varepsilon$ and $B=\beta\varepsilon$, and let $\varepsilon\to0$, assuming no triple junctions. Formally matched asymptotics give a free-boundary problem: Darcy flow and reaction–diffusion in each phase domain, and on each interface $\Gamma_{ij}$ jump and velocity conditions involving the surface tension $\gamma_{ij}$ and the mean curvature $\kappa$. For two phases (host $H$, tumour $T$) with $\Psi=4\varphi_1^2\varphi_2^2$ and $N=\frac{\chi_\sigma}2\sigma^2+2\chi_\varphi\sigma\varphi_1$, the interface conditions are

$$[\vec v]^T_H\cdot\vec\nu=0,\qquad [\tilde\mu]^T_H=0,\qquad [p]^T_H=\beta\gamma\kappa,\qquad [\sigma]^T_H=2\frac{\chi_\varphi}{\chi_\sigma},\qquad \beta\gamma\kappa=2\tilde\mu+\frac{\chi_\sigma}{2}\big[\sigma^2\big]^T_H,$$

together with the normal-velocity laws $2(-\mathcal V+\vec v\cdot\vec\nu)=[m\nabla\mu]^T_H\cdot\vec\nu$ and $(-\mathcal V+\vec v\cdot\vec\nu)[\sigma]^T_H=\chi_\sigma[n\nabla\sigma]^T_H\cdot\vec\nu$. Here $\mathcal V$ is the interface velocity, $m,n$ are the mobilities, and the surface tension is $\gamma=\int_{-1}^1\sqrt{2\tilde\Psi(s)}\,ds=\frac{2\sqrt2}{3}$ with $\tilde\Psi(s)=\frac14(1-s^2)^2$. This recovers the two-phase sharp-interface tumour model, including a Young–Laplace pressure jump.

Numerical finite element simulations of the three-phase model, with host, proliferating and necrotic phases, are used to study how necrosis affects tumour growth.

## Expansion

The energy identity follows by differentiating $\mathcal E$ in time and substituting the equations. The $\bm\varphi$-transport term combines with the Darcy law, $|\vec v|^2/K=-\vec v\cdot\nabla p+\vec v\cdot(\nabla\bm\varphi)^\top(\bm\mu-N_{,\bm\varphi})$, and $\operatorname{div}\vec v=\mathbf 1\cdot\bm U$ produces the pressure term. Using the volume-averaged velocity instead of the mass-averaged one makes the incompressibility constraint linear, $\operatorname{div}\vec v=\mathbf 1\cdot\bm U$, which simplifies the system considerably. In the asymptotics, the leading-order inner problem is the heteroclinic profile $\phi''=\tilde\Psi'(\phi)$, that is $\phi(z)=\tanh(z/\sqrt2)$, whose energy is the surface tension. The first-order solvability condition gives the Gibbs–Thomson-type relation between $\kappa$, the chemical potential and the jump of $\sigma^2$.

These are the energy theorem and remark of Section 2.3, the sharp-interface derivation of Section 3, and the numerical study of Section 4 of the source.

## Sources

- H. Garcke, K. F. Lam, R. Nürnberg, E. Sitka, "A multiphase Cahn–Hilliard–Darcy model for tumour growth with necrosis", arXiv:1701.06656 (2017). <https://doi.org/10.48550/arXiv.1701.06656>
