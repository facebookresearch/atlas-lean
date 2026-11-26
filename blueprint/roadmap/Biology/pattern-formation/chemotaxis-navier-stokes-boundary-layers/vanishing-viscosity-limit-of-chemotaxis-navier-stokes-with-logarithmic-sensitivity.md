# Vanishing-viscosity limit of chemotaxis–Navier–Stokes with logarithmic sensitivity

**Model.** In the half-plane $\{(x,y):y>0\}$ consider aerobic bacteria (density $n$) consuming oxygen (concentration $c>0$) in an incompressible fluid (velocity $u$, pressure $p$), with logarithmic chemotactic sensitivity:
$$\partial_tn=\Delta n-u\cdot\nabla n-\chi\nabla\cdot\Big(\frac{n}{c}\nabla c\Big),\qquad \partial_tc=\varepsilon\Delta c-u\cdot\nabla c-nc,$$
$$\partial_tu=\varepsilon\Delta u-(u\cdot\nabla)u-\nabla p+n\,e_2,\qquad \nabla\cdot u=0,$$
where $\varepsilon\ge0$ is both the chemical diffusion and the viscosity. For $\varepsilon>0$ impose the zero-flux and Navier slip conditions $\partial_yn+n\partial_yc=0$, $\partial_yc=0$, $\partial_yu_1=0$, $u_2=0$ on $y=0$; for $\varepsilon=0$ only $\partial_yn+n\partial_yc=0$ and $u_2=0$. The Cole–Hopf variable $v=-\nabla\ln c$ turns the singular sensitivity into a nonsingular coupling.

**Theorem.** Let $(n_{\mathrm{in}},\ln c_{\mathrm{in}},u_{\mathrm{in}})\in H^{14}\times H^{15}\times H^{15}$ with $n_{\mathrm{in}}\ge0$, $c_{\mathrm{in}}>0$, and let $(n^0,c^0,u^0)$ be the inviscid ($\varepsilon=0$) solution on $[0,T]$. Then for all small $\varepsilon>0$ the viscous problem has a unique solution on $[0,T]$ and, with $C$ independent of $\varepsilon$,
$$\sup_{t\le T}\|n^\varepsilon-n^0\|_{L^\infty}\le C\varepsilon^{1/4},\qquad \sup_{t\le T}\|u^\varepsilon-u^0\|_{L^\infty}\le C\varepsilon^{1/2},$$
$$\sup_{t\le T}\|c^\varepsilon-c^0\|_{L^2}\le C\varepsilon^{1/2},\qquad \sup_{t\le T}\|c^\varepsilon-c^0\|_{L^\infty}\le C\varepsilon^{1/4},$$
while the gradient variable has a boundary layer of width $\sqrt\varepsilon$:
$$\sup_{t\le T}\Big\|v^\varepsilon-v^0-\big(0,v_2^{B,0}\big)\big(t,x,\tfrac{y}{\sqrt\varepsilon}\big)\Big\|_{L^\infty}\le C\varepsilon^{1/4},$$
with an explicit inner profile $v_2^{B,0}$.

## Expansion

Because the inviscid problem cannot satisfy the Neumann condition on $c$ (equivalently $v_2=0$), the viscous solution develops a layer in the normal component of $v=-\nabla\ln c$ near the water–air surface $y=0$, which is where aerobic bacteria accumulate. One builds an approximate solution as outer profile plus inner profiles in the stretched variable $y/\sqrt\varepsilon$ up to order $\varepsilon$, writes the true solution as approximation plus $\varepsilon^{1/2}$ times a remainder, and closes uniform estimates for the remainder in conormal Sobolev spaces, which control tangential derivatives without paying for normal derivatives across the layer. Anisotropic Sobolev embedding converts the $L^2$ remainder bounds into the $L^\infty$ rates.

## Sources

- Hui Wang, Lingling Zhao, "Boundary layer analysis for the 2D Chemotaxis-Navier-Stokes system with logarithmic sensitivity, Part II. viscous vanishing limit", arXiv:2609.11027 (2026), Theorems 1.1, 1.2 and 2.1–2.3, <https://doi.org/10.48550/arXiv.2609.11027>.
