# Coexistence and exclusion of phytoplankton competing for the light spectrum

**Model.** In a water column $0 < x < L$ (depth $x$) with sufficient nutrients, two phytoplankton species with densities $u_1, u_2$ satisfy

$$\partial_t u_i = D_i\,\partial_x^2 u_i - \alpha_i\,\partial_x u_i + \big[g_i(\gamma_i(x,t)) - d_i(x)\big]u_i,\qquad D_i\partial_x u_i - \alpha_i u_i = 0 \text{ at } x = 0, L,$$

with turbulent diffusion $D_i > 0$, sinking/buoyancy velocity $\alpha_i \in \mathbb{R}$, death rate $d_i \in C([0,L])$, and increasing saturating growth $g_i$ ($g_i(0) = 0$, $g_i' > 0$, $g_i(\infty) < \infty$, e.g. Monod). Light is a continuum of resources over wavelengths $\lambda \in [400, 700]$ nm: with absorption spectra $k_i(\lambda)$, incident spectrum $I_{\rm in}(\lambda)$ and background attenuation $K_{BG}(\lambda)$, Lambert–Beer's law gives

$$I(\lambda,x,t) = I_{\rm in}(\lambda)\exp\Big[-K_{BG}(\lambda)x - \sum_j k_j(\lambda)\int_0^x u_j(y,t)\,dy\Big],\qquad \gamma_i(x,t) = \int_{400}^{700}k_i(\lambda)I(\lambda,x,t)\,d\lambda.$$

**Persistence threshold.** Let $f_i(x,p_1,p_2) = g_i\big(\int k_i I_{\rm in}e^{-K_{BG}x - k_1p_1 - k_2p_2}\,d\lambda\big) - d_i(x)$ and let $\mu(D,\alpha,h)$ be the principal eigenvalue of $D\phi'' - \alpha\phi' + h\phi + \mu\phi = 0$ with $D\phi' - \alpha\phi = 0$ at $0, L$. If $\mu(D_i,\alpha_i,f_i(\cdot,0,0)) < 0$ for $i = 1,2$ (condition (P); sufficient: $\int_0^L e^{\alpha_i x/D_i}f_i(x,0,0)\,dx > 0$), there are exactly two exclusion equilibria $E_1 = (\tilde{u}_1, 0)$ and $E_2 = (0, \tilde{u}_2)$, each attracting the solutions in which only its species is initially present.

**Coexistence.** Let $\mu_u = \mu\big(D_2,\alpha_2,f_2(x,\int_0^x\tilde{u}_1,0)\big)$ and $\mu_v = \mu\big(D_1,\alpha_1,f_1(x,0,\int_0^x\tilde{u}_2)\big)$ be the invasion eigenvalues. If $\mu_u < 0$ and $\mu_v < 0$, the system is uniformly persistent ($\liminf_{t\to\infty}\min_i\int_0^L u_i \ge \delta_0 > 0$ independently of initial data) and has a locally asymptotically stable coexistence equilibrium.

**Niche differentiation index.** Define $\mathcal{I}_S(k_1,k_2) = \|k_1 - k_2\|_{L^1}/(\|k_1\|_{L^1} + \|k_2\|_{L^1}) \in [0,1]$.

- If $\mathcal{I}_S = 1$ (disjoint absorption spectra), condition (P) alone implies the coexistence conclusions, since each species is then invisible to the other's light.
- If $\mathcal{I}_S = 0$ (identical spectra), with $f_1 = f_2$ and $d_1 = d_2$: for $D_1 = D_2$ and $\alpha_1 < \alpha_2$ species 1 excludes species 2; for $D_1 < D_2$ and $\alpha_1 = \alpha_2 \ge [f_1(L,0,0) - d_1]L$ (strong sinking) the faster diffuser wins; in each case exclusion holds from all initial data, and other advection regimes can favor the slower diffuser instead.

## Expansion

Light in the column is consumed from the top down, so each species shades the other only through the wavelengths both absorb. When spectra do not overlap the invader's growth environment is unchanged by the resident, so its invasion eigenvalue equals its persistence eigenvalue and mutual invasibility follows; the monotone (competitive) structure then yields persistence and a stable coexistence state via the theory of monotone semiflows. Identical spectra reduce the problem to the single-resource water-column model, where competitive exclusion holds with the winner set by advection and diffusion. Intermediate overlap and turbidity, studied numerically, interpolate between these extremes, resolving part of the paradox of the plankton.

## Sources

- Christopher M. Heggerud, King-Yeung Lam and Hao Wang, "Niche differentiation in the light spectrum promotes coexistence of phytoplankton species: a spatial modelling approach", Journal of Mathematical Biology 86 (2023), 54, <https://doi.org/10.1007/s00285-023-01890-z>; numbering as in arXiv:2109.02634: Definition 3.1, Proposition 3.2, Corollary 3.3, Propositions 3.4 and 3.6, Definition 4.1, Corollary 4.2 and Theorems 4.3 and 4.4 (recalled from earlier work).
