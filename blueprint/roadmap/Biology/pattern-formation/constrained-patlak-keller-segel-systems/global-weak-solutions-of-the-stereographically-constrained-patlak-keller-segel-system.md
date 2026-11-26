# Global weak solutions of the stereographically constrained Patlak–Keller–Segel system below $16\pi$

The planar parabolic–elliptic Patlak–Keller–Segel (PKS) system for a cell density $\rho$ with chemotactic sensitivity $\chi$,

$$\partial_t\rho=\Delta\rho-\chi\nabla\cdot(\rho\nabla u),\qquad u(x,t)=-\frac{1}{2\pi}\int_{\mathbb{R}^2}\ln|x-y|\,\rho(y,t)\,dy ,$$

with unit mass is the Wasserstein gradient flow of the log-HLS free energy

$$\mathcal{F}_\chi(\rho)=\int_{\mathbb{R}^2}\rho\ln\rho\,dx+\frac{\chi}{4\pi}\iint\rho(x)\ln|x-y|\,\rho(y)\,dx\,dy ,$$

and has critical value $\chi=8\pi$ (global existence for $\chi\le8\pi$, finite-time blow-up for $\chi>8\pi$).

Let $\mathcal{S}(x)=\frac{1}{1+|x|^2}(2x_1,2x_2,|x|^2-1)$ be the inverse stereographic projection and

$$\mathring{\Gamma}=\Big\{\rho\ge0:\int\rho=1,\ \int\rho\ln\rho<\infty,\ \int|x|^2\rho<\infty,\ \int\mathcal{S}(x)\rho(x)\,dx=0\Big\},$$

densities whose lift to the sphere has its centre of mass at the origin.

**Constrained log-HLS inequality.** For every $\alpha\ge\tfrac12$ there is $C(\alpha)$ with

$$\int\rho\ln\rho\,dx+\frac{2}{\alpha}\iint\rho(x)\ln|x-y|\,\rho(y)\,dx\,dy+\Big(2-\frac{2}{\alpha}\Big)\int\rho\ln(1+|x|^2)\,dx\ge-C(\alpha)\qquad(\rho\in\mathring{\Gamma}).$$

With $\chi/(4\pi)=2/\alpha$ this gives a lower bound for $\mathcal{F}_\chi$ on $\mathring{\Gamma}$ for $8\pi\le\chi\le16\pi$.

**Constrained flow.** The Wasserstein gradient flow of $\mathcal{F}_\chi$ restricted to $\mathring{\Gamma}$ is the PKS system with a time-dependent Lagrange multiplier $\boldsymbol{\lambda}(t)\in\mathbb{R}^3$,

$$\partial_t\rho=\Delta\rho-\chi\nabla\cdot\Big[\rho\,\nabla\Big(u+\tfrac{1}{\chi}\boldsymbol{\lambda}(t)\cdot\mathcal{S}\Big)\Big],\qquad \mathcal{A}[\rho]\,\boldsymbol{\lambda}=-\boldsymbol{b}[\rho],$$

where $\mathcal{A}[\rho]_{ij}=\int\rho\,\nabla\mathcal{S}_i\cdot\nabla\mathcal{S}_j\,dx$ is positive definite for every finite-entropy $\rho$ (so $\boldsymbol{\lambda}$ is determined by $\rho$) and $\boldsymbol{b}[\rho]_i=-\int\rho\,\Delta\mathcal{S}_i+\frac{\chi}{4\pi}\iint(\nabla\mathcal{S}_i(x)-\nabla\mathcal{S}_i(y))\cdot\frac{x-y}{|x-y|^2}\rho(x)\rho(y)\,dx\,dy$. The constraint $\int\mathcal{S}\rho=0$ is preserved and $\mathcal{F}_\chi$ decreases along the flow.

**Statement.** If $\chi<16\pi$ and $\rho_0\in\mathring{\Gamma}$, the constrained PKS system has a global weak solution. The centre-of-mass constraint thus doubles the critical sensitivity from $8\pi$ to $16\pi$.

## Expansion

The weak solution is built by the JKO minimizing-movement scheme $\rho^{k+1}\in\arg\min_{\mathring{\Gamma}}\{\mathcal{F}_\chi(\rho)+W_2^2(\rho,\rho^k)/(2h)\}$. For $\chi<16\pi$ the constrained log-HLS inequality (applied with some $\alpha>\tfrac12$) bounds the entropy and second moment of the iterates uniformly, which gives compactness, a uniform positive lower bound on $\mathcal{A}[\rho]$, and passage to the limit in the Euler–Lagrange equation. The inequality itself is proved on $\mathbb{S}^2$, where it is dual to the Moser–Aubin inequality under a vanishing first moment, and transferred to the plane by stereographic projection. The authors state that the global multiplier has no known biological mechanism; the constraint is a mathematical device for suppressing chemotactic collapse.

## Sources

- M. Ghosh, D. Karmakar, R. Sinha and K. Verma, *A constrained log-HLS inequality and its associated Wasserstein flow*, arXiv:2610.05356 (2026), <https://doi.org/10.48550/arXiv.2610.05356>. Theorem 1.4 (global weak solution); Theorem 4.4 (log-HLS inequality on $\mathring{\Gamma}$); Section 5 (constrained Wasserstein flow and the constrained PKS system); Section 6 (constrained JKO scheme).
