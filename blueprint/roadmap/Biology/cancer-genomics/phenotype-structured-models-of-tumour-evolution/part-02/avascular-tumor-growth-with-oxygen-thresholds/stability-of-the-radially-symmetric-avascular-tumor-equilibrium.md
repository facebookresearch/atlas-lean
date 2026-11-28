# Stability of the radially symmetric avascular tumor equilibrium

**Model.** In a two-dimensional mean-field model of an avascular tumor, cells at constant density $\rho = 1$ consume oxygen, whose concentration $c$ solves the stationary equation $-\Delta c = -\lambda$ in living tissue ($c \ge \kappa_{\mathrm{death}}$) and $-\Delta c = 0$ elsewhere, with $c = 1$ on the circle $r = R = 1$ (the oxygen source; the external tissue consumes no oxygen). Cells proliferate at rate $\mu_{\mathrm{prol}} = 1$ where $c \ge \kappa_{\mathrm{prol}}$, are quiescent where $\kappa_{\mathrm{death}} \le c < \kappa_{\mathrm{prol}}$, and die at rate $\mu_{\mathrm{death}} > 0$ where $c < \kappa_{\mathrm{death}}$, with $0 < \kappa_{\mathrm{death}} < \kappa_{\mathrm{prol}} < 1$; growth moves cells by Darcy flow, $-\Delta p = \Gamma$. For a radially symmetric tumor let $r_p$ be its radius and $r_q$, $r_n$ the radii of the proliferative/quiescent and quiescent/necrotic interfaces, $0 \le r_n \le r_q \le r_p < 1$.

**Regional relations and dynamics.** The oxygen field is explicit,

$$c(r) = 1 + \frac{\lambda}{2}\big(r_p^2 - r_n^2\big)\log r \quad (r \ge r_p), \qquad c(r) = 1 + \frac{\lambda}{2}\Big(r_p^2 \log r_p - r_n^2 \log r + \frac{r^2 - r_p^2}{2}\Big) \quad (r_n \le r \le r_p),$$

and the threshold conditions $c(r_q) = \kappa_{\mathrm{prol}}$, $c(r_n) = \kappa_{\mathrm{death}}$ give

$$K_{\mathrm{prol}} := \frac{4(1 - \kappa_{\mathrm{prol}})}{\lambda} = -r_p^2\log r_p^2 + r_n^2 \log r_q^2 - r_q^2 + r_p^2, \qquad K_{\mathrm{death}} := \frac{4(1 - \kappa_{\mathrm{death}})}{\lambda} = -r_p^2\log r_p^2 + r_n^2\log r_n^2 - r_n^2 + r_p^2.$$

Mass balance $\dot V = V_p - \mu_{\mathrm{death}} V_n$ yields

$$\frac{d}{dt}\big(r_p^2\big) = r_p^2 - r_q^2 - \mu_{\mathrm{death}}\, r_n^2,$$

so $r_p(0)$ and $(K_{\mathrm{prol}}, K_{\mathrm{death}}, \mu_{\mathrm{death}})$ determine the radial dynamics.

**Proposition.** Let $\mu_{\mathrm{death}} > 0$ and let $0 \le r_n^* \le r_q^* \le r_p^*$ be a stationary solution of these relations. Linearizing the radius equation about it gives the single eigenvalue

$$\Lambda_r = 1 - \frac{\log r_p^*}{\log r_n^*}\Big(\mu_{\mathrm{death}} + \frac{2\log(r_q^*/r_n^*)}{(r_q^*)^2 - (r_n^*)^2}\,(r_q^*)^2\Big),$$

and $\Lambda_r < 0$ (the stationary tumor is stable to radial perturbations) whenever $r_p^* \le e^{-1} \approx 0.368$.

## Expansion

The radial eigenvalue follows by implicitly differentiating the two algebraic threshold relations to express $r_q^2$ and $r_n^2$ as functions of $r_p^2$ and inserting them in the linearized area equation. For the bound, write $(r_n^*)^2 = \eta (r_q^*)^2$ with $\eta \in (0,1)$; stationarity gives $(r_p^*)^2 = (1 + \mu_{\mathrm{death}}\eta)(r_q^*)^2$, and $\Lambda_r$ becomes a function of $(\eta, \mu_{\mathrm{death}}, r_p^*)$ that is decreasing in $\mu_{\mathrm{death}}$ and increasing in $r_p^*$. Bounding by $\mu_{\mathrm{death}} \to 0^+$ and $r_p^* = e^{-1}$ leaves $\Lambda_r < 1 + \frac{\log\eta}{(1 - \frac12\log\eta)(1-\eta)}$, which is negative by the elementary inequality $-y \le (e^{-y} - 1)(1 + y/2)$ for $y = -\log\eta \ge 0$. Stability to non-radial (angular mode $k$) perturbations of the outer boundary is a separate question: there the same model with perturbed interfaces $r_p + \epsilon\, \zeta_p \cos(k\theta)$ shows which modes grow, which explains when the tumor fingers or stays round. The cell-based stochastic counterpart of the model reproduces these regimes.

## Proof depends on

- [Implicit function theorem](../../../../../Analysis/real-functions/multivariable-calculus/implicit-function-theorem.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- E. Blom and S. Engblom, "Morphological stability for in silico models of avascular tumors", arXiv:2309.07889 (2023), Section 2.3 (mean-field PDE model: oxygen law, source term, pressure law), Section 3.1 (radial relations, radial dynamics, eigenvalue and Proposition 3.1) and Section 3.2 (Theorem 3.2, linear morphological stability), <https://doi.org/10.48550/arXiv.2309.07889>.
