# Orlicz bounds excluding blow-up under anisotropic signal production

**Model.** In a smoothly bounded domain $\Omega\subset\mathbb R^n$ with $n\le5$, consider the Keller–Segel system with an anisotropic correction to signal production,
$$u_t=D\Delta u-\nabla\cdot(u\nabla v),\qquad v_t=d\Delta v+\nabla\cdot(u\nabla v)-v+u,$$
with homogeneous Neumann boundary conditions, cell diffusivity $D>0$ and signal diffusivity $d>0$. The extra term $+\nabla\cdot(u\nabla v)$ removes the classical Lyapunov functional and makes the signal equation degenerate.

**Theorem.** Let $D>0$ and $d>0$ be arbitrary and $K>0$. There exist $\alpha=\alpha(K)>0$ and $C(K)>0$ such that for all nonnegative $u_0,v_0\in W^{1,\infty}(\Omega)$ with $\|u_0\|_{L^\infty}+\|v_0\|_{L^\infty}\le K$ there is a global weak solution $(u,v)$, nonnegative with $u,v\in L^2_{\mathrm{loc}}([0,\infty);W^{1,2}(\Omega))$, satisfying
$$\int_\Omega e^{u^\alpha(\cdot,t)}\le C(K)\quad\text{and}\quad\|v(\cdot,t)\|_{L^\infty(\Omega)}\le C(K)\qquad\text{for a.e. }t>0.$$

In particular $\sup_t\|u(\cdot,t)\|_{L^p}<\infty$ for every finite $p$, so no $L^p$ blow-up occurs in finite or infinite time. This contrasts with the classical Keller–Segel system ($v_t=d\Delta v-v+u$), where for $n\ge2$ finite-time explosion occurs in every $L^p$ with $p>n/2$; the anisotropic correction prevents collapse even when the cell and signal diffusion rates differ strongly.

## Expansion

Adding the two equations shows that $w=u+v$ satisfies a parabolic equation without cross-diffusion except through the diffusivities, since the taxis terms cancel. The proof follows functionals of the form
$$\int_\Omega v^2e^{(w+1)^\alpha}+b\int_\Omega(w+1)e^{(w+1)^\alpha},\qquad b>0,$$
which involve only zero-order quantities and so avoid the diffusion degeneracy. For small $\alpha$ these satisfy an absorptive differential inequality along regularized problems, giving time-independent bounds in an exponential Orlicz class; a Moser-type iteration bounds $v$, and compactness passes to a weak solution.

## Sources

- Youshan Tao, Michael Winkler, "Preventing $L^p$ blow-up by local anisotropy of signal production in the Keller-Segel system with strongly differing diffusion rates", arXiv:2606.06009 (2026), Theorem 2.1 and Corollary 2.7, <https://doi.org/10.48550/arXiv.2606.06009>.
