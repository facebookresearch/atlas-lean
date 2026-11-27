# Global weak solutions of the Cahn–Hilliard–Darcy tumour model with chemotaxis

**Model.** In a bounded domain $\Omega \subset \mathbb R^d$ ($d = 2,3$, $C^3$ boundary), tumour and healthy cells form an inertia-less mixture with order parameter $\varphi \in [-1,1]$ ($\varphi = 1$ tumour, $\varphi = -1$ healthy tissue), chemical potential $\mu$, nutrient concentration $\sigma$, volume-averaged velocity $\boldsymbol v$ and pressure $p$:

$$\operatorname{div}\boldsymbol v = \Gamma_{\boldsymbol v}, \qquad \boldsymbol v = -K\big(\nabla p - (\mu + \chi\sigma)\nabla\varphi\big),$$

$$\partial_t\varphi + \operatorname{div}(\varphi\boldsymbol v) = \operatorname{div}\big(m(\varphi)\nabla\mu\big) + \Gamma_\varphi, \qquad \mu = A\Psi'(\varphi) - B\Delta\varphi - \chi\sigma,$$

$$\partial_t\sigma + \operatorname{div}(\sigma\boldsymbol v) = \operatorname{div}\big(n(\varphi)(D\nabla\sigma - \chi\nabla\varphi)\big) - \mathcal S,$$

with permeability $K$, chemotaxis/active-transport coefficient $\chi$, mobilities $m, n$, a double-well potential $\Psi$, mass sources $\Gamma_{\boldsymbol v}, \Gamma_\varphi$ (proliferation, apoptosis), nutrient consumption $\mathcal S$, and a Robin condition $n(\varphi)D\partial_\nu\sigma = b(\sigma_\infty - \sigma)$ for the nutrient. The nutrient couples to the tumour through fluxes, sources and Darcy's law.

**Theorem (existence, $d=3$).** Under the paper's growth assumptions there is a global weak solution satisfying an energy inequality with

$$\varphi \in L^\infty(H^1)\cap L^2(H^3)\cap W^{1,8/5}\big((H^1)^*\big), \quad \sigma \in L^\infty(L^2)\cap L^2(H^1), \quad \mu \in L^2(H^1),$$

$$p \in L^{8/5}(H^1)\cap L^{8/7}(H^2), \qquad \boldsymbol v \in L^2(\boldsymbol L^2)\cap L^{8/7}(\boldsymbol H^1),$$

with bounds uniform in $b,\chi \in (0,1]$, and uniform in $K \in (0,1]$ when $\Gamma_{\boldsymbol v} = 0$ (with $K^{-1/2}$ weights on the velocity terms).

**Theorem (existence, $d=2$).** In two dimensions a refined velocity regularity gives better time integrability, e.g. $p \in L^q(H^2)$ and $\boldsymbol v \in L^q(\boldsymbol H^1)$ for every $q<4/3$, and $\partial_t\varphi \in L^w((H^1)^*)$ for $w<2$.

**Theorem (singular limits).** (i) *Vanishing permeability:* if $\Gamma_{\boldsymbol v} = 0$, then as $b,K \to 0$ the velocity tends to $0$ strongly in $L^2(\boldsymbol L^2)\cap L^{8/7}(\boldsymbol H^1)$ and the remaining variables converge to a weak solution of the Cahn–Hilliard–nutrient system without convection. (ii) *Vanishing chemotaxis:* as $b,\chi \to 0$, solutions converge to a weak solution of the Cahn–Hilliard–Darcy system without chemotaxis and active transport.

## Expansion

The proof uses a Galerkin approximation and the energy

$$\int_\Omega A\Psi(\varphi) + \tfrac B2|\nabla\varphi|^2 + \tfrac D2|\sigma|^2 + \chi\sigma(1-\varphi)\,dx,$$

whose dissipation controls $\nabla\mu$, $\nabla\sigma$ and $K^{-1}|\boldsymbol v|^2$. The Darcy coupling only gives $\boldsymbol v \in L^2(\boldsymbol L^2)$, so the convective terms $\operatorname{div}(\varphi\boldsymbol v)$ and $\operatorname{div}(\sigma\boldsymbol v)$ have weaker time regularity than in Cahn–Hilliard–reaction–diffusion systems; elliptic regularity for the pressure equation recovers the $H^1$ velocity bound, and the uniformity of the estimates in $K$ and $\chi$ yields the singular limits.

## Sources

- Harald Garcke and Kei Fong Lam, "Global weak solutions and asymptotic limits of a Cahn--Hilliard--Darcy system modelling tumour growth", arXiv:1608.08758 (2016), Theorem 2.1 (existence in 3D and energy inequality), Theorem 2.2 (existence in 2D), Theorem 2.3 (vanishing permeability), Theorem 2.4 (vanishing chemotaxis), <https://doi.org/10.48550/arXiv.1608.08758>.
