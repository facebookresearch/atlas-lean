# τ-independent logistic damping threshold for Keller–Segel boundedness

Let $\Omega\subset\mathbb R^N$ ($N\ge1$) be a bounded convex domain with smooth boundary and consider the fully parabolic Keller–Segel system with quadratic logistic growth,

$$u_t=\Delta u-\chi\nabla\cdot(u\nabla v)+\lambda u-\mu u^2,\qquad \tau v_t=\Delta v-v+u,$$

with homogeneous Neumann conditions, $\chi,\mu,\tau>0$, $\lambda\in\mathbb R$, and nonnegative data $u_0\in C(\overline\Omega)$, $v_0\in W^{1,\infty}(\Omega)$.

**Theorem.** If

$$\mu>\frac{N\chi}{4},$$

then for every $\tau>0$ there is a unique nonnegative global classical solution with $\sup_{t>0}\big(\|u(t)\|_{L^\infty}+\|v(t)\|_{W^{1,\infty}}\big)<\infty$. With $\delta=\mu-N\chi/4$ and $C_*=\frac{(\lambda+\tau^{-1})_+^2}{4\delta}$, the absorbing bounds are

$$\limsup_{t\to\infty}\|u(t)\|_{L^\infty}\le\frac{\big((\tau-1)\lambda+\chi\tau C_*\big)_+}{(\tau-1)\mu+\chi}\ \ (\tau>1),\qquad \limsup_{t\to\infty}\|u(t)\|_{L^\infty}\le C_*\ \ (\tau=1).$$

The explicit damping condition $\mu>N\chi/4$, previously known only for equal cell and signal diffusivities ($\tau=1$), therefore prevents chemotactic collapse for every ratio of diffusivities and in every dimension. For general coefficients $u_t=d_1\Delta u-\chi\nabla\cdot(u\nabla v)+\lambda u-\mu u^2$, $v_t=d_2\Delta v-\beta v+\alpha u$, rescaling turns it into $\mu>N\alpha\chi/(4d_1)$.

## Expansion

When $\tau=1$ the quantity $Z=\frac12|\nabla v|^2+\frac1\chi u$ satisfies a closed scalar parabolic inequality on convex domains (convexity makes $\partial_\nu|\nabla v|^2\le0$), and comparison with an ODE gives boundedness exactly when $\mu>N\chi/4$, the $N/4$ coming from $|\Delta v|^2\le N|D^2v|^2$. For $\tau\ne1$ the two equations diffuse at different speeds and this closure fails. The proof builds an auxiliary comparison function adapted to the mismatch and derives its differential inequality. For $\tau\ge1$ (slow signal) this already closes pointwise. For $0<\tau<1$ it gives pointwise control only after parabolic squeezing, so Hölder regularity of the signal and Hölder–Sobolev interpolation are needed to finish the boundedness argument. Biologically, quadratic crowding-induced death strong enough relative to the chemotactic sensitivity always stops aggregation, whatever the signal's relative diffusivity.

## Sources

- J. Jiang, *An Explicit Logistic Damping Criterion for Boundedness in a Fully Parabolic Keller--Segel System* (2026), Theorem 1.1 and Remark 1.2 (general constant coefficients); proof in Sections 3–5. <https://doi.org/10.48550/arXiv.2608.03869>
