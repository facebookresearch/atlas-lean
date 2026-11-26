# Homogenized macroscopic model of plant tissue growth

**Setting.** Consider the microscopic morphoelastic model of a plant tissue with periodic cell-wall microstructure of period $\delta$ (wall domain $\Omega^\delta$, unit cell $Y$ with wall part $Y_w$ and cell-interior boundary $\Gamma$), turgor pressure $P_1(t,x)+\delta P_2(t,x,x/\delta)$, multiplicative growth $\mathbf F=\mathbf F_e\mathbf F_g$, elastic strain $\boldsymbol\varepsilon^{\rm el}(\nabla\mathbf u,\mathbf F_g^{-1})=\operatorname{sym}(\nabla\mathbf u\,\mathbf F_g^{-1})+\operatorname{sym}(\mathbf F_g^{-1})-\mathbf I$, and thresholded stress- or strain-driven growth $\partial_t\mathbf F_{g,\delta}=G^\delta\,\mathbf F_{g,\delta}$, $\mathbf F_{g,\delta}(0)=\mathbf I$, with $G^\delta$ the entrywise truncation to $[-M,M]$ of $\eta_\sigma[\fint\boldsymbol\sigma-\boldsymbol\tau_\sigma]_+$ or $\eta_\varepsilon[\fint\boldsymbol\varepsilon^{\rm el}-\boldsymbol\tau_\varepsilon]_+$.

**Cell problems and effective tensors.** For $(t,x)$ fixed, let $\mathbf w^{ij}$ and $\mathbf v$ be $Y$-periodic solutions on $Y_w$ of

$$\operatorname{div}_y\Big(J_g\,\mathbb E(x,y)\big(\operatorname{sym}(\nabla_y\mathbf w^{ij}\mathbf F_g^{-1})+\mathbf b_{ij}\big)\mathbf F_g^{-T}\Big)=0,\qquad \operatorname{div}_y\Big(J_g\big(\mathbb E(x,y)\operatorname{sym}(\nabla_y\mathbf v\,\mathbf F_g^{-1})+\mathbf I\big)\mathbf F_g^{-T}\Big)=0,$$

with zero conormal flux on $\Gamma$, where $\mathbf b_{ij}$ are the elementary symmetric matrices. Define

$$\mathbb E_{\rm hom,ijkl}=\frac1{|Y|}\int_{Y_w}\Big(\mathbb E_{ijkl}(x,y)+\big[\mathbb E(x,y)\operatorname{sym}(\nabla_y\mathbf w^{ij}\mathbf F_g^{-1})\big]_{kl}\Big)dy,\qquad K_{\rm hom}=\frac1{|Y|}\int_{Y_w}\mathbb E(x,y)\operatorname{sym}(\nabla_y\mathbf v\,\mathbf F_g^{-1})\,dy,$$

and $\boldsymbol\sigma_{\rm hom}=\mathbb E_{\rm hom}\,\boldsymbol\varepsilon^{\rm el}(\nabla\mathbf u,\mathbf F_g^{-1})+K_{\rm hom}P_1$. The effective tensors depend on time through the growth tensor.

**Theorem.** Assume the hypotheses of the microscopic well-posedness theorem and, in addition, the $\delta$-uniform bound $\|\mathcal T^\delta(\nabla\mathbf u^\delta)\|_{L^\infty((0,T)\times\Omega;L^2(Y_w))}\le C$ on the periodically unfolded displacement gradients. Then, up to a subsequence, $\mathbf u^\delta\rightharpoonup\mathbf u$ weakly-$\ast$ in $L^\infty(0,T;V)$ and $\mathbf F_{g,\delta}\rightharpoonup\mathbf F_g$ weakly-$\ast$ in $L^\infty((0,T)\times\Omega)\cap W^{1,\infty}(0,T;L^q(\Omega))$, $q\in(1,\infty)$, where $(\mathbf u,\mathbf F_g)$ solves the macroscopic problem

$$\operatorname{div}_x\big(J_g\,\boldsymbol\sigma_{\rm hom}\,\mathbf F_g^{-T}\big)=J_g\,\mathbf F_g^{-T}\,\frac1{|Y|}\int_\Gamma P_2(t,x,y)\,N\,d\gamma_y\quad\text{in }(0,T)\times\Omega,$$

$$J_g\,\boldsymbol\sigma_{\rm hom}\mathbf F_g^{-T}N=\Big(1-\frac{|Y_w|}{|Y|}\Big)J_gP_1\,\mathbf F_g^{-T}N+J_g\,|\mathbf F_g^{-T}N|\,\mathbf f\quad\text{on }\Gamma_N,$$

with the corresponding Dirichlet or sliding condition on $\Gamma_D$, coupled to the macroscopic growth law

$$\partial_t\mathbf F_g=G(x,\nabla\mathbf u,\mathbf F_g^{-1})\,\mathbf F_g,\qquad \mathbf F_g(0)=\mathbf I,$$

where $G$ truncates $\eta_\sigma\big[\tfrac{|Y|}{|Y_w|}\boldsymbol\sigma_{\rm hom}-\boldsymbol\tau_\sigma\big]_+$ (stress-driven) or $\eta_\varepsilon\big[\tfrac{|Y|}{|Y_w|}\boldsymbol\varepsilon_{\rm hom}-\boldsymbol\tau_\varepsilon\big]_+$ (strain-driven), $\boldsymbol\varepsilon_{\rm hom}$ being the cell average of the corrected microscopic strain. If in addition $\|\nabla\mathbf u\|_{L^\infty((0,T)\times\Omega)}\le C$, the macroscopic solution is unique and the whole sequence converges.

## Expansion

The $\delta$-uniform bounds of the microscopic theory give weak-$\ast$ limits, and two-scale convergence gives $\nabla\mathbf u^\delta\rightharpoonup\nabla\mathbf u+\nabla_y\mathbf u_1$ with a periodic corrector $\mathbf u_1$. Because the growth law uses cell averages, $\mathbf F_{g,\delta}$ is constant on cells and its periodic unfolding has no fast dependence, so the growth equation can be passed to the limit once the cell-averaged unfolded strains converge strongly in $L^2$; the extra bound on $\mathcal T^\delta(\nabla\mathbf u^\delta)$ yields this strong convergence together with $\mathbf F_{g,\delta}\to\mathbf F_g$ strongly in $L^2$. The corrector is linear in the macroscopic elastic strain and in $P_1$, $\mathbf u_1=\sum_{ij}\boldsymbol\varepsilon^{\rm el}_{ij}\mathbf w^{ij}+P_1\mathbf v$, which produces $\mathbb E_{\rm hom}$ and $K_{\rm hom}$; the order-$\delta$ pressure fluctuation $P_2$ survives as a body force through its average over $\Gamma$, and the wall volume fraction $|Y_w|/|Y|$ weights the boundary turgor. The macroscopic tensors are computed on the grown cell $\mathbf F_gY$ and pulled back to the fixed cell $Y_w$. Uniqueness requires the extra Lipschitz control given by the $L^\infty$ bound on $\nabla\mathbf u$.

This is Theorem 3.1 of the source, which also compares two-scale numerical simulations with the microscopic model.

## Depends on

- [Well-posedness of the microscopic morphoelastic model of plant tissue growth](well-posedness-of-the-microscopic-plant-tissue-growth-model.md)

## Sources

- A. Boudaoud, A. Kiss, M. Ptashnyk, *Multiscale modelling and analysis of growth of plant tissues*, arXiv:2302.08449 (2023). <https://doi.org/10.48550/arXiv.2302.08449>
