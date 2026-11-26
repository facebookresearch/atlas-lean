# Forward stability of variational turning-kernel estimation across kinetic and Keller–Segel scales

**Model.** In one dimension, bacteria run with speed $\pm v$ and tumble with a turning kernel $T_\epsilon=T_0(x)\pm\epsilon T_1(x)$, where $T_0>0$ is symmetric and $T_1$ antisymmetric in direction, and $T_0\pm\epsilon T_1>0$. Here $\epsilon$ is the ratio of microscopic to macroscopic scales. In diffusive scaling the densities $f^\pm$ of right- and left-movers give the density $\rho=f^++f^-$ and flux $J=(f^+-f^-)/\epsilon$, which satisfy the **two-flux model**

$$\partial_t\rho+v\,\partial_xJ=0,\qquad \epsilon^2\partial_tJ+v\,\partial_x\rho=-2T_0(x)J-2T_1(x)\rho .$$

As $\epsilon\to0$, $J_0=-\frac{v\partial_x\rho_0}{2T_0}-\frac{T_1\rho_0}{T_0}$, and $\rho_0$ solves the Keller–Segel-type Fokker–Planck equation

$$\partial_t\rho_0+\partial_x\Big[\Big(-\frac{vT_1}{T_0}-\frac{v^2\partial_xT_0}{2T_0^2}\Big)\rho_0\Big]-\partial_x^2\Big[\frac{v^2}{2T_0}\rho_0\Big]=0 .$$

$T_0$ sets the diffusion $v^2/(2T_0)$, and $T_1$ the chemotactic drift $-vT_1/T_0$.

**Loss functionals.** Given observed $(\rho,J)$, the weighted losses

$$\mathcal E[\hat T_1]=\frac1T\int_0^T\!\!\int_{\mathbb R}|\hat T_1-T_1|^2\frac{\rho}{T_0^2}\,dx\,dt,\qquad \mathcal G[\hat T_0]=\frac1T\int_0^T\!\!\int_{\mathbb R}|\hat T_0-T_0|^2J^2\,dx\,dt$$

can be computed without knowing the true kernel. Expanding the square and using the flux equation replaces $2T_1\rho$, respectively $2T_0J$, by observable combinations of $\epsilon^2\partial_tJ$, $v\partial_x\rho$ and the other kernel component. As $\epsilon\to0$, $\mathcal E$ tends to $\mathcal E_0=\frac1T\iint|\hat T_1/T_0-T_1/T_0|^2\rho_0$, a loss on the macroscopic drift, and $\mathcal G$ tends to $\mathcal G_0=\frac1T\iint|\hat T_0-T_0|^2J_0^2$.

**Theorem.**

1. *(Kinetic scale.)* Let $(\rho,J)$ and $(\hat\rho,\hat J)$ solve the two-flux model with $(T_0,T_1)$ and $(\hat T_0,\hat T_1)$. Suppose $\rho T_0^2$ is bounded and $\hat T_0,\hat T_1$ are bounded. Then

$$\|\bar\rho(T)\|_{L^2}^2+\|\bar J(T)\|_{L^2}^2\le C_1\|\bar\rho(0)\|_{L^2}^2+C_2\|\bar J(0)\|_{L^2}^2+C_3\,\mathcal E[\hat T_1]+C_4\,\mathcal G[\hat T_0],$$

with constants $C_i(\epsilon,T)$ that diverge as $\epsilon\to0$.
2. *(Macroscopic scale, Wasserstein.)* Let $\mu_t,\hat\mu_t$ be the laws of the limiting densities. Suppose the estimated drift $\frac{v\hat T_1}{\hat T_0}+\frac{v^2\partial_x\hat T_0}{2\hat T_0^2}$ and diffusion $v/\sqrt{\hat T_0}$ are Lipschitz with constants $L_1,L_2$. Then

$$d_2^2(\mu_T,\hat\mu_T)\le C^0_1d_2^2(\mu_0,\hat\mu_0)+C^0_2\int_0^T\!\!\int|b-\hat b|^2\,d\mu_t\,dt+C^0_3\int_0^T\!\!\int\Big|\frac{v}{\sqrt{T_0}}-\frac{v}{\sqrt{\hat T_0}}\Big|^2d\mu_t\,dt,$$

where $b,\hat b$ are the true and estimated drifts and $C^0_i=C^0_i(T,L_1,L_2)$ do not depend on $\epsilon$.
3. *(Macroscopic flux.)* Under $L^\infty$ bounds on $\hat T_0$, $\partial_x(\hat T_1/\hat T_0)$ and $\partial_x(1/\hat T_0)$, the limiting fluxes satisfy an $L^2$ stability estimate with $\epsilon$-independent constants. Assume further that $T_0,\hat T_0$ lie in a common finite basis $\{\Psi_i\}$ and that the data are informative, $\iint|\sum_id_i\Psi_i|^2J_0^2\ge\kappa\sum_i d_i^2$. Then $\iint|T_0-\hat T_0|^2|\partial_tJ_0|^2\le\frac{M_J}{\kappa}\iint|T_0-\hat T_0|^2J_0^2$, and hence $\|\bar J_0(T)\|^2\le C^0_4\|\bar J_0(0)\|^2+C^0_6\,\mathcal G_0[\hat T_0]$.

Combine item 2 with an interpolation $\|\rho_0-\hat\rho_0\|_{L^2}^2\le C_rd_2^{2\beta}$ ($0<\beta<1$) under uniform Sobolev regularity, and with the $O(\epsilon)$ kinetic-to-diffusive approximation error away from layers. This gives a *conditional scale-uniform* estimate:

$$\|\rho(T)-\hat\rho(T)\|_{L^2}^{2/\beta}\le O(\epsilon^{1/\beta})+3C^0_1d_2^2(\mu_0,\hat\mu_0)+3C^0_2v^2T\,\mathcal E_0[\hat T_1].$$

A small loss then yields a small forward error uniformly in $\epsilon$, even though the kinetic constants in item 1 blow up.

## Expansion

Item 1 integrates the two transport equations along the characteristics $x\mp vt/\epsilon$. This writes $\bar\rho$ and $\bar J$ as transported initial differences plus time integrals of $\epsilon^{-1}\big[(T_1\rho-\hat T_1\hat\rho)+(T_0J-\hat T_0\hat J)\big]$ (with an extra $\epsilon^{-1}$ for $\bar J$). Splitting off the kernel errors $(T_1-\hat T_1)\rho$ and $(T_0-\hat T_0)J$, which are controlled by $\mathcal E$ and $\mathcal G$, and estimating the remaining terms in $L^2$ gives the bound. The negative powers of $\epsilon$ are why the constants degenerate. Item 2 is a synchronous coupling: the limiting equation is the law of $dX_t=b(X_t)\,dt+\frac{v}{\sqrt{T_0}}(X_t)\,dB_t$, and coupling the true and estimated SDEs with the same Brownian motion, then applying Itô's formula and Gronwall's lemma, bounds $\mathbb E|X_T-\hat X_T|^2$. The data-informativeness Gram condition is what lets the observable loss $\mathcal G_0$ control a time-derivative-weighted discrepancy. The choice of weight $\rho/T_0^2$ in $\mathcal E$ makes one functional recover both the kinetic kernel $T_1$ and the macroscopic drift $T_1/T_0$, which is the source of the uniformity.

These are Theorems 1–2, the Gram-matrix lemmas, and the conditional uniform-stability analysis of Section 3 of the source.

## Sources

- J. A. Carrillo, J. Ma, M. Tang, "Bridging Scales in Chemotaxis: Scale-Uniform Forward Stability for Run-and-Tumble Kernel Estimation", arXiv:2608.06390 (2026). <https://doi.org/10.48550/arXiv.2608.06390>
