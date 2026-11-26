# Growth dichotomy and joint free boundary of a tumor–nutrient system with sublinear reactions

**Model.** Tumor cells of density $\rho\ge0$ consume a nutrient $v\ge0$ with sublinear rates $\gamma,\theta\in(0,1)$:

$$\rho_t-\operatorname{div}(\rho\,Dp)=\rho\,v^\gamma,\qquad v_t-\Delta v=-\rho\,v^\theta .$$

In the Hele–Shaw (incompressible) limit $\rho\le1$; near the saturated region $\rho$ is bounded away from $0$, and freezing coefficients for the density defect $u=1-\rho$ gives the prototype system in $Q_1=B_1\times(-1,1)$:

$$\Delta u-u_t=v^\gamma,\qquad \Delta v-v_t=v^\theta,\qquad u,v\ge0 .$$

With $\beta=2/(1-\theta)$ and $\alpha=2+\gamma\beta=2(1-\theta+\gamma)/(1-\theta)$ the system is invariant under $u\mapsto r^{-\alpha}u(x_0+rx,t_0+r^2t)$, $v\mapsto r^{-\beta}v(x_0+rx,t_0+r^2t)$; set $|(u,v)|=u^{1/\alpha}+v^{1/\beta}$. Using backward (past-accessible) free boundaries, let $\Gamma_u$ be the **saturation interface**, $\Gamma_v$ the **nutrient depletion interface**, and $\Gamma$ the **joint free boundary** of $|(u,v)|$.

**Theorem.** Let $(u,v)\ge0$ be a bounded weak solution.
1. *(Coupling.)* $\Gamma=\Gamma_u\cap\{v=0\}=\Gamma_v\cap\{u=0\}=\Gamma_u\cap\Gamma_v$.
2. *(Optimal joint growth.)* There is $C$ depending only on $\gamma,\theta,n,\|u\|_\infty,\|v\|_\infty$ such that at every $z_0\in\Gamma\cap Q^-_{1/2}$, $\sup_{Q^-_r(z_0)}|(u,v)|\le Cr$, i.e. $u\le Cr^\alpha$ and $v\le Cr^\beta$.
3. *(Quadratic–superquadratic dichotomy.)* There are universal $C,r_0>0$ such that for $z_0\in\Gamma_u$ and $0<r<r_0$,

$$\sup_{Q_r(z_0)}u\le C\,r^2\,\varphi(z_0,r),\qquad \varphi(z,r)=\begin{cases}v^\gamma(z)+r^\gamma,& z\in\Gamma_u\setminus\Gamma,\\ r^{\gamma\beta},& z\in\Gamma.\end{cases}$$

So $\Gamma_u=\mathcal{Q}\cup\Gamma$: at points of $\mathcal{Q}=\Gamma_u\setminus\Gamma$ the nutrient is positive and $u$ has a nontrivial quadratic blow-up, while at joint points $u$ grows superquadratically like $r^\alpha$, $\alpha>2$.
4. *(Regular points.)* The joint interface has zero space-time measure; the regular sets satisfy $\mathcal{R}_u=\Gamma\cap\mathcal{R}_v$; a half-space blow-up of either component determines the joint blow-up $|(u_{r,z_0},v_{r,z_0})|\to C_{\theta,\gamma}(x\cdot\nu)_+$; and near regular points the joint and nutrient free boundaries coincide in a backward neighborhood, so the joint interface is $C^{1,\sigma}$ in space and $C^{1/2}$ in time.

## Expansion

The nutrient equation decouples, so the known parabolic dead-core theory for $\Delta v-v_t=v^\theta$ gives growth $v\lesssim r^\beta$ at its free boundary. The density defect solves a heat equation forced by $v^\gamma$: where $v(z_0)>0$ the forcing is a positive constant at leading order and $u$ looks like a quadratic polynomial, while where $v$ also vanishes the forcing is $O(r^{\gamma\beta})$ and integrating twice gives $r^{2+\gamma\beta}=r^\alpha$. Saturation-interface regularity is therefore only possible at joint points, where the backward coincidence with the nutrient interface transfers its regularity.

## Sources

- Damião J. Araújo, Rafayel Teymurazyan and José Miguel Urbano, "Tumor growth models with nutrient consumption", arXiv:2610.37144 (2026), Proposition 3.2, Corollary 3.3, Theorem 4.2, Corollary 4.6 and Sections 5–7, <https://doi.org/10.48550/arXiv.2610.37144>.
