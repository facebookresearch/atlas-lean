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

with $\nu = o(T^{-1})$ (the parameter setting (6) of the source). Let the kernels be rescalings of fixed profiles,

$$\phi(x) = \sigma_\phi^{-1}\,\varphi\big(x/\sigma_\phi\big), \qquad \phi_1(x) = \tilde\sigma_{\phi_1}^{-1}\,\varphi_1\big(x/\tilde\sigma_{\phi_1}\big),$$

where $\varphi$ and $\varphi_1$ do not depend on $T$, have finite moments of all orders and decay exponentially as $|x| \to \infty$, and the scale factors $\sigma_\phi, \tilde\sigma_{\phi_1} > 0$, which depend on $T$, give the kernels the moments required above (Eqs. (10)–(12) of the source). Writing $P v = v_t - \Gamma v - h_1(v)$ for the PDE operator ($\Gamma = \operatorname{diag}(\partial_x^2,\ \nu\partial_x + d\partial_x^2)$, $h_1$ the reaction terms) and $P_T$ for the operator whose zeros sampled at $t = nT$ solve the integrodifference model, one has $Pv(x,t) - P_Tv(x,t) \to 0$ as $T \to 0^+$ at every point, for every smooth $v$ whose derivatives grow at most polynomially. Consistency is equation-level; convergence of solutions is supported numerically but not proved.

This corrects Proposition 1 as printed, which assumes only that "the kernel functions ϕ and ϕ1 have finite moments of all orders and decay exponentially as |x| → ∞" and concludes "Pv − P_T v → 0 as T → 0+, for any v ∈ C∞(R × [0,∞), [0,∞)²)". Those hypotheses do not say how the kernels' shape may vary with $T$, and they do not suffice: the mixture of centred Gaussians with variances $T/(1-T)$ and $1$ and weights $1-T$ and $T$ has variance $2T$, finite moments of all orders and exponential tails, but fourth moment $3T + O(T^2)$, and for $u = x^4$, $w = 0$ the plant convolution at $x = 0$ leaves a discrepancy of order one after division by $T$, while $u_{xx}(0) = 0$. The source's proof uses the fixed-profile rescaling stated above.

## Expansion

At steady state $u^2w = Bu$ and $A = w + u^2w$, so $uw = B$ and $u(A - Bu) = B$, a quadratic with roots $\bar u_{2,3}$ requiring $A \ge 2B$; the integrodifference model has the same fixed points because $C\phi * f(\bar u,\bar w) = C f(\bar u, \bar w) = \bar u$ when the reaction terms vanish. For consistency, expand $f(u,w)(x - y, t)$ under the convolution in a second-order Taylor polynomial in $y$ with remainder: the kernel's zeroth moment returns $u + T(u^2w - Bu)$, its second moment $\sigma_\phi^2/2 = T$ produces $T u_{xx}$, and for $\phi_1$ the mean and second moment produce $T(\nu w_x + d w_{xx})$. For derivatives of polynomial growth the remainder is bounded by $C(x)\,|y|^3(1 + |y|^m)$ for some $m$, so its integral against either kernel is bounded by absolute moments of order at least $3$, which are $O(T^{3/2}) = o(T)$ for fixed-profile kernels, because the $j$-th absolute moment of a profile rescaled by a factor of order $\sqrt T$ is $O(T^{j/2})$; dividing the one-step increment by $T$ therefore recovers the PDE. The same expansion in $t$ handles $v_t$.

*Remark.* The argument uses the fixed profiles only through the bound on the remainder, so it applies verbatim to any $T$-indexed kernel families $\phi_T$, $\phi_{1,T}$ with the moments of the parameter setting above whose absolute moments of every order $j \ge 3$ are $o(T)$ as $T \to 0^+$. This moment form is the page's own extension; the source does not state it.

## Sources

- L. Eigentler and J. A. Sherratt, "An integrodifference model for vegetation patterns in semi-arid environments with seasonality", Journal of Mathematical Biology (2020), Section 2, Equations (1) and (5)–(12), Proposition 1 and its proof, <https://doi.org/10.1007/s00285-020-01530-w> (PMC7519009).
- C. A. Klausmeier, "Regular and irregular patterns in semiarid vegetation", Science 284 (1999), 1826–1828, <https://doi.org/10.1126/science.284.5421.1826>.
