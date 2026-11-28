# Well-posedness of the microscopic morphoelastic model of plant tissue growth

**Model.** A plant tissue occupies a bounded domain $\Omega\subset\mathbb R^d$ ($d=2,3$; Lipschitz convex or $C^{1,\tilde\gamma}$) in the reference configuration. Its periodic microstructure at scale $\delta$ consists of cell walls and middle lamellae $\Omega^\delta$ (translates of a unit-cell wall domain $\delta Y_w$) surrounding cell interiors with boundaries $\Gamma^\delta$, on which the turgor pressure $P^\delta(t,x)=P_1(t,x)+\delta P_2(t,x,x/\delta)$ acts. The deformation gradient splits multiplicatively, $\mathbf F=\mathbf I+\nabla\mathbf u=\mathbf F_e\mathbf F_g$, and the walls are linearly elastic in the elastic strain

$$\boldsymbol\varepsilon^{\rm el}(\nabla\mathbf u,\mathbf F_g^{-1})=\operatorname{sym}(\nabla\mathbf u\,\mathbf F_g^{-1})+\operatorname{sym}(\mathbf F_g^{-1})-\mathbf I,\qquad \mathbf S_\delta=\mathbb E(x,x/\delta)\,\boldsymbol\varepsilon^{\rm el}.$$

The displacement $\mathbf u^\delta$ satisfies quasi-static equilibrium in the reference configuration,

$$-\operatorname{div}\big(J_g^\delta\,\mathbf S_\delta^T\,\mathbf F_{g,\delta}^{-T}\big)=0\ \text{ in }\Omega^\delta,\qquad J_g^\delta\,\mathbf S_\delta^T\mathbf F_{g,\delta}^{-T}N=-J_g^\delta P^\delta\,\mathbf F_{g,\delta}^{-T}N\ \text{ on }\Gamma^\delta,$$

with $J_g^\delta=\det\mathbf F_{g,\delta}$, a traction $\mathbf f$ on $\Gamma_N$, and either $\mathbf u^\delta=0$ or a sliding condition on $\Gamma_D$. Growth is driven by cell-averaged stress or strain above a threshold:

$$\partial_t\mathbf F_{g,\delta}=G^\delta(x,\nabla\mathbf u^\delta,\mathbf F_{g,\delta}^{-1})\,\mathbf F_{g,\delta},\qquad \mathbf F_{g,\delta}(0)=\mathbf I,$$

where $\tilde G^\delta=\eta_\sigma\big[\fint_{\text{cell}}\boldsymbol\sigma-\boldsymbol\tau_\sigma\big]_+$ (or the same with $\boldsymbol\varepsilon^{\rm el}$ and a strain threshold $\boldsymbol\tau_\varepsilon$), the average being over the wall part of the cell containing $x$, and $G^\delta$ truncates each entry of $\tilde G^\delta$ to $[-M,M]$. Thus $\mathbf F_{g,\delta}$ is piecewise constant on cells.

**Assumptions.** $\mathbb E\in C^\gamma(\overline\Omega;L^\infty_{\rm per}(Y))$ is uniformly positive definite and bounded on symmetric matrices with minor and major symmetries; $\mathbf f\in C^\gamma([0,T]\times\partial\Omega)$, $P_1\in C^\gamma([0,T];C^1(\overline\Omega))$, $P_2\in C^\gamma([0,T]\times\overline\Omega\times\Gamma)$, $Y$-periodic in the last variable.

**Korn-type inequality.** If $\mathbf F\in L^\infty$ is constant on each cell, $\det\mathbf F\ge1$ and all eigenvalues of $\mathbf F$ are at least $1$, then for admissible $\mathbf u$

$$\|\mathbf u\|^2_{L^2(\Omega^\delta)}+\|\nabla\mathbf u\|^2_{L^2(\Omega^\delta)}\le C(\mathbf F)\,\|\operatorname{sym}(\nabla\mathbf u\,\mathbf F^{-1})\|^2_{L^2(\Omega^\delta)},$$

with $C$ independent of $\delta$.

**Theorem.** Under these assumptions the microscopic problem has a unique weak solution $\mathbf u^\delta\in L^2(0,T;V_\delta)$, $\mathbf F_{g,\delta}\in W^{1,\infty}(0,T;L^q(\Omega^\delta))\cap L^\infty((0,T)\times\Omega^\delta)$ for every $q\in(1,\infty)$, and

$$\|\mathbf u^\delta\|_{L^\infty(0,T;V_\delta)}+\|\mathbf F_{g,\delta}\|_{L^\infty}+\|\partial_t\mathbf F_{g,\delta}\|_{L^\infty}+\|\mathbf F_{g,\delta}\|_{W^{1,\infty}(0,T;L^q)}\le C,$$

with $C$ independent of $\delta$.

## Expansion

Because growth only enlarges cells ($\det\mathbf F_g\ge1$, eigenvalues $\ge1$, which the thresholded positive-part law preserves), the reference domain sits inside the grown configuration, and a cell-by-cell change of variables plus the standard periodic extension operator from walls to whole cells reduces the twisted Korn inequality to the classical one with $\delta$-uniform constants. The existence proof is a Banach fixed-point argument on the set of admissible growth tensors bounded by $\hat\kappa\ge e^{dMT}$: given $\tilde{\mathbf F}_g$, the elasticity problem is coercive by the Korn-type inequality and a scaled trace estimate $\delta\|v\|^2_{L^2(\Gamma^\delta)}\le C(\|v\|^2+\delta^2\|\nabla v\|^2)$ handles the turgor term; the truncated growth ODE then produces a new admissible $\mathbf F_g$, and the Lipschitz dependence of the cell-averaged stress or strain on $\mathbf F_g$ makes this map a contraction. The truncation by $M$ yields the uniform $L^\infty$ bound on $\partial_t\mathbf F_g$.

These are Lemma 2.3 (Korn-type inequality) and Theorem 2.4 (well-posedness) of the source.

## Sources

- A. Boudaoud, A. Kiss, M. Ptashnyk, *Multiscale modelling and analysis of growth of plant tissues*, arXiv:2302.08449 (2023). <https://doi.org/10.48550/arXiv.2302.08449>
