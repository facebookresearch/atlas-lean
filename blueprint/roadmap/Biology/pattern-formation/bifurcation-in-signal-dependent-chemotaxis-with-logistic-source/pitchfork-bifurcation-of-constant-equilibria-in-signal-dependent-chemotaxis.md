# Pitchfork bifurcation of constant equilibria in signal-dependent chemotaxis

**Model.** On $(0,L)$ with Neumann conditions, consider

$$u_t = u_{xx} - \chi_0\Big(\frac{u^m}{(1+v)^\beta}v_x\Big)_x + au - bu^{1+\alpha}, \qquad 0 = v_{xx} - \mu v + \nu u^\gamma,$$

with $\alpha, \gamma, m, \mu, \nu > 0$, $a, b, \beta \ge 0$ and $\chi_0 \in \mathbb{R}$. Either $a, b > 0$ (non-minimal model, $u^* = (a/b)^{1/\alpha}$) or $a = b = 0$ (minimal model, any $u^* > 0$, with perturbations of zero mean); in both cases $v^* = \nu (u^*)^\gamma/\mu$. With Neumann eigenvalues $\lambda_n = n^2\pi^2/L^2$ and eigenfunctions $\phi_n = \cos(n\pi x/L)$, the linearization at $(u^*,v^*)$ has eigenvalues

$$\sigma_n(\chi_0) = -\lambda_n + \chi_0\,\nu\gamma\,\frac{(u^*)^{m+\gamma-1}}{(1+v^*)^\beta}\,\frac{\lambda_n}{\mu+\lambda_n} - a\alpha,$$

and the constant state is linearly stable for $\chi_0 < \chi^*$ and unstable for $\chi_0 > \chi^*$, where

$$\chi^*(u^*) = \inf_{n\ge1}\chi_n(u^*), \qquad \chi_n(u^*) = \frac{(1+v^*)^\beta}{\nu\gamma(u^*)^{m+\gamma-1}}\,\frac{(\lambda_n + a\alpha)(\mu + \lambda_n)}{\lambda_n}.$$

A mode $n_0 \ge 1$ with $\chi_{n_0} = \chi^*$ is a bifurcation mode; it is unique when $L \in (L_{k-1}, L_k)$ with $L_0 = 0$, $L_k = \pi\sqrt{k(k+1)}/(a\alpha\mu)^{1/4}$ (then $n_0 = k$), and for the minimal model $n_0 = 1$ for every $L$.

**Theorem (local pitchfork).** Let $n_0$ be the unique bifurcation mode and $\alpha_{n_0} = \partial_{\chi_0}\sigma_{n_0}(\chi^*) = \nu\gamma\,(u^*)^{m+\gamma-1}(1+v^*)^{-\beta}\lambda_{n_0}/(\mu + \lambda_{n_0}) > 0$. There is an explicit number $\beta_{n_0}$, depending on $u^*$ and all parameters, such that if $\beta_{n_0} \ne 0$, two curves $\Gamma^\pm_{n_0}$ of nonconstant stationary solutions bifurcate from $(u^*,v^*)$ at $\chi_0 = \chi^*$, with

$$u^\pm = u^* \pm \sqrt{\frac{\alpha_{n_0}}{\beta_{n_0}}(\chi_0 - \chi^*)}\,\phi_{n_0} + O(|\chi_0 - \chi^*|), \qquad v^\pm = v^* \pm \frac{\nu\gamma(u^*)^{\gamma-1}}{\lambda_{n_0} + \mu}\sqrt{\frac{\alpha_{n_0}}{\beta_{n_0}}(\chi_0 - \chi^*)}\,\phi_{n_0} + O(|\chi_0 - \chi^*|).$$

If $\beta_{n_0} > 0$ the bifurcation is super-critical ($\chi_0 > \chi^*$) and the bifurcating states are linearly exponentially stable; if $\beta_{n_0} < 0$ it is sub-critical ($\chi_0 < \chi^*$) and they are unstable.

**Theorem (effect of $\beta$ and $L$).** With all other parameters fixed, $\beta_{n_0}(\beta) = A\beta^2 + B\beta + C$ with $A < 0$. Hence the bifurcation is always sub-critical for $\beta$ large; depending on $B, C$ it is super-critical exactly on an interval $[0,\beta_+)$ or $(\beta_-,\beta_+)$, or never. Since $\chi^* \propto (1+v^*)^\beta$, a larger $\beta$ also requires a proportionately larger sensitivity to destabilize the constant state. With all parameters but $L$ fixed and $L$ in an admissible interval, $\beta_{n_0}$ is an explicit rational function $P(\lambda_{n_0})/Q(\lambda_{n_0})$ of $\lambda_{n_0} = \pi^2 n_0^2/L^2$.

## Depends on

- [Chemotactic instability criterion for the Keller–Segel model](../turing-instability-with-cross-diffusion/keller-segel-turing-iff.md)

## Expansion

Expanding $u - u^*$ and $v - v^*$ in the cosine basis, center manifold reduction near $\chi^*$ yields the scalar normal form

$$\dot u_{n_0} = \alpha_{n_0}(\chi_0 - \chi^*)\,u_{n_0} - \beta_{n_0}u_{n_0}^3 + O\big(|u_{n_0}|^2|\chi_0 - \chi^*|^2 + |u_{n_0}|^3|\chi_0 - \chi^*| + |u_{n_0}|^4\big),$$

and the sign of the cubic coefficient $\beta_{n_0}$ decides the direction. Its closed form is a quadratic polynomial in $\beta$ with negative leading coefficient, which is why strong signal saturation always makes the transition sub-critical, i.e. abrupt and hysteretic. Crandall–Rabinowitz theory gives an alternative proof of the local branches but not this explicit coefficient.

## Sources

- L. Chen, I. Ruau and W. Shen, "Chemotaxis models with signal-dependent sensitivity and a logistic-type source, III: Bifurcation and spike-like solutions", arXiv:2610.20976 (2026), Proposition 1.1, Theorems 1.1 and 1.2, and Remark 1.1, proved in Sections 2 and 3, <https://doi.org/10.48550/arXiv.2610.20976>.
