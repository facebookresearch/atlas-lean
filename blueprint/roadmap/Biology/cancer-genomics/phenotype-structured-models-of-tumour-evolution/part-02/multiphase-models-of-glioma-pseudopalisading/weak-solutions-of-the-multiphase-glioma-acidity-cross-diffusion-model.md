# Weak solutions of the multiphase glioma–acidity cross-diffusion model

**Derivation.** Brain tissue near a glioma is a saturated mixture of glioma cells $u_c$, normal tissue $u_m$, necrotic matter $u_n$ and interstitial fluid $u_w$ ($\sum u_i=1$), with proton concentration $h$. Each phase obeys mass balance $\partial_tu_i+\nabla\cdot J_i=f_i$ and an inertia-free momentum balance with common pressure $p$, phase-specific extra pressures $\tau_i$, and interphase drag $K_{ij}(u_iJ_j-u_jJ_i)$:

$$
\nabla(u_i\tau_i)+u_i\nabla p=\sum_{j\ne i}K_{ij}(u_iJ_j-u_jJ_i).
$$

Non-living phases carry no extra pressure ($\tau_n=\tau_w=0$), while

$$
\tau_c=\alpha_cu_c+g(h),\quad g(h)=\frac{\chi h}{1+h/h_{\max}},\qquad \tau_m=\alpha_m(1+\theta u_c)u_m ,
$$

so acidity raises glioma pressure (saturating, repellent pH-taxis) and tumour cells compress the tissue. Solving the linear drag system for the fluxes (an explicit inverse of the reduced drag matrix) and neglecting the fluid phase gives the reaction–cross-diffusion system, with $u_n=1-u_c-u_m$,

$$
\begin{aligned}
\partial_tu_c&=\nabla\cdot\big(a_{cc}\nabla(u_c\tau_c)+a_{cm}\nabla(u_m\tau_m)-J_{\rm sum}u_c\big)+f_c,\\
\partial_tu_m&=\nabla\cdot\big(a_{mc}\nabla(u_c\tau_c)+a_{mm}\nabla(u_m\tau_m)-J_{\rm sum}u_m\big)+f_m,\qquad
\partial_th=D_h\Delta h+f_h,
\end{aligned}
$$

where the $a_{ij}=a_{ij}(u_c,u_m)$ are explicit rational functions of the volume fractions and of $\varepsilon_c=K_{cn}/K_{cm}-1$, $\varepsilon_m=K_{mn}/K_{cm}-1$, with $a_{cc},a_{mm}\ge0\ge a_{cm},a_{mc}$, and $J_{\rm sum}=\sum_iJ_i$ is any divergence-free field ($J_{\rm sum}=0$ in 1D with no-flux boundaries).

**Theorem.** Let $0<K_{cm}\le K_{cn}\le K_{mn}$ and $\alpha_c,\alpha_m,\theta,h_{\max},\chi>0$ satisfy two explicit positivity conditions (minima over $y\in[0,1]$ of two quartic polynomials in $y$ built from $\alpha_c,\alpha_m,\theta,\varepsilon_c,\varepsilon_m$ must be positive). Let $\mathcal D=\{(u_c,u_m,h):u_c,u_m>0,\ u_c+u_m<1,\ h>0\}$ (the source's (4.1a)), and let $f_c,f_m,f_h$ be Lipschitz on $\overline{\mathcal D}$ with $f_i\ge0$ when $u_i=0$ ($i=c,m$), $f_c+f_m\le0$ when $u_c+u_m=1$, and $f_h\ge0$ when $h=0$. Then for every $J_{\rm sum}\in L^2_{\rm loc}([0,\infty);L^2(\Omega)^N)$ and initial data $(u_{c0},u_{m0},h_0)\in L^\infty(\Omega)^2\times L^2(\Omega)$ with values in $\mathcal D$ for a.e. $x\in\Omega$, the system with no-flux boundary conditions has a global weak solution $(u_c,u_m,h):[0,\infty)\times\Omega\to\mathcal D$ in the sense of the source's (4.13)–(4.14): $(u_c,u_m,h)\in L^2_{\rm loc}([0,\infty);H^1(\Omega)^3)$, $\partial_t(u_c,u_m,h)\in L^2_{\rm loc}([0,\infty);(H^1(\Omega)^3)')$, the three equations hold in weak form against every test function in $H^1(\Omega)^3$ for a.e. $t$, and the initial data are taken in the $L^2(\Omega)$ sense.

The source's (4.12b) prints $f_c+f_n\le0$ on $\{u_c+u_m=1\}$; the condition $f_c+f_m\le0$ used here follows from its (3.1) ($\sum_if_i\equiv0$) and $f_i\ge0$ at $u_i=0$, since on that set $u_n=u_w=0$, so $f_c+f_m=-f_n-f_w\le0$, and it is the condition that keeps $u_c+u_m\le1$.

## Expansion

The existence proof follows the boundedness-by-entropy method: with the entropy density $E=u_c\ln u_c+u_m\ln u_m+u_n\ln u_n+\tfrac a2h^2$, whose Hessian is

$$
D^2E=\begin{pmatrix}\frac{1-u_m}{u_nu_c}&\frac1{u_n}&0\\ \frac1{u_n}&\frac{1-u_c}{u_nu_m}&0\\0&0&a\end{pmatrix},
$$

the two quartic conditions guarantee that $(D^2E)M$ is uniformly positive definite on $\mathcal D$ for the diffusion matrix $M$ of the system. Working in entropy variables then keeps volume fractions in $[0,1]$ automatically, and compactness yields weak solutions. Unlike earlier 1D multiphase models, the derivation allows unequal drag coefficients and any space dimension, and it lets normal and necrotic tissue be displaced by population and biochemical pressure, producing nonlinear diffusion and drift for these phases rather than ODEs. Numerically, acidity-driven pressure pushes glioma cells away from acidic, necrotic cores, producing the garland-like pseudopalisade patterns of high-grade gliomas.

## Sources

- Pawan Kumar, Christina Surulescu, Anna Zhigun, "Multiphase modelling of glioma pseudopalisading under acidosis", arXiv:2106.15241 (2021), Section 3 (mass and momentum balances, choices of $\tau_c,\tau_m$, Lemma 3.3, model and Remarks 3.4–3.6), Section 4 (positivity conditions, Lemma 4.2, Theorem 4.3), Section 5 (numerical study), <https://doi.org/10.48550/arXiv.2106.15241>.
