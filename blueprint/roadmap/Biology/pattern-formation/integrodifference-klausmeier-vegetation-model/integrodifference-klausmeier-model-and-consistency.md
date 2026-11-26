# Integrodifference Klausmeier model and its consistency with the PDE model

**Local Klausmeier model.** With plant density $u(x,t) \ge 0$, water density $w(x,t) \ge 0$, $x \in \mathbb R$ increasing uphill, rainfall $A > 0$, plant mortality $B > 0$, downhill flow speed $\nu \ge 0$ and water diffusivity $d > 0$, the nondimensional model is
$$u_t = u^2 w - Bu + u_{xx}, \qquad w_t = A - w - u^2 w + \nu w_x + d\,w_{xx}.$$

**Integrodifference model.** Separating each season into a growth phase without dispersal and a dispersal phase, the densities $u_n, w_n$ after $n$ steps satisfy
$$u_{n+1} = C\,\phi * f(u_n, w_n),\qquad w_{n+1} = D\,\phi_1 * g(u_n, w_n),$$
$$f(u,w) = u^2w - Bu + \tfrac1C u,\qquad g(u,w) = A - u^2 w - w + \tfrac1D w,$$
where $\phi$ is a symmetric plant-dispersal kernel, $\phi_1$ a water-redistribution kernel with mean $\mu_{\phi_1} \le 0$ (symmetric on flat ground), and $C, D > 0$ scale the growth step. The spatially uniform steady states coincide with those of the PDE: the desert $(0, A)$ and, for $A > 2B$,
$$\bar u_{2,3} = \frac{A \pm \sqrt{A^2 - 4B^2}}{2B},\qquad \bar w_{2,3} = \frac{A \mp \sqrt{A^2-4B^2}}{2},$$
the vegetated state $(\bar u_2, \bar w_2)$ (larger $\bar u$) being the one that can be stable to homogeneous perturbations.

**Proposition (consistency).** Let the step length be $T > 0$ and set
$$C = T,\quad \sigma_\phi^2 = 2T,\quad D = T,\quad \mu_{\phi_1} = -\nu T,\quad \int x^2\phi_1(x)\,dx = 2dT,$$
with $\nu = o(T^{-1})$, and let $\phi, \phi_1$ have finite moments of all orders and decay exponentially. Writing $P v = v_t - \Gamma v - h_1(v)$ for the PDE operator ($\Gamma = \operatorname{diag}(\partial_x^2,\ \nu\partial_x + d\partial_x^2)$, $h_1$ the reaction terms) and $P_T$ for the operator whose zeros sampled at $t = nT$ solve the integrodifference model, one has $Pv - P_Tv \to 0$ as $T \to 0^+$ for every smooth $v$. Consistency is equation-level; convergence of solutions is supported numerically but not proved.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

At steady state $u^2w = Bu$ and $A = w + u^2w$, so $uw = B$ and $u(A - Bu) = B$, a quadratic with roots $\bar u_{2,3}$ requiring $A \ge 2B$; the integrodifference model has the same fixed points because $C\phi * f(\bar u,\bar w) = C f(\bar u, \bar w) = \bar u$ when the reaction terms vanish. For consistency, expand $f(u,w)(x - y, t)$ under the convolution in Taylor series and integrate term by term (Watson's lemma): the kernel's zeroth moment returns $u + T(u^2w - Bu)$, its second moment $\sigma_\phi^2/2 = T$ produces $T u_{xx}$, and for $\phi_1$ the mean and second moment produce $T(\nu w_x + d w_{xx})$; higher moments are $O(T^{3/2})$ or smaller under the scalings, so dividing the one-step increment by $T$ recovers the PDE.

## Sources

- L. Eigentler and J. A. Sherratt, "An integrodifference model for vegetation patterns in semi-arid environments with seasonality", Journal of Mathematical Biology (2020), Section 2, Equations (1) and (5)–(8), Proposition 1 and its proof, <https://doi.org/10.1007/s00285-020-01530-w> (PMC7519009).
- C. A. Klausmeier, "Regular and irregular patterns in semiarid vegetation", Science 284 (1999), 1826–1828, <https://doi.org/10.1126/science.284.5421.1826>.
