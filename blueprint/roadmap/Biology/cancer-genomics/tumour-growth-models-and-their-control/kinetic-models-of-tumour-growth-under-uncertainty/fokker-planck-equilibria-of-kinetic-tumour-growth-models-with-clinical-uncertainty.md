# Fokker–Planck equilibria of kinetic tumour growth models with clinical uncertainty

**Setting.** A tumour is described by its volume $x > 0$, and all uncertain clinical parameters are collected in a random vector $\mathbf{z}$ with density $\rho(\mathbf{z})$. In one microscopic transition of size $\epsilon$ the volume changes as $x' = x + \Phi^\epsilon_\delta(x/x_L,\mathbf{z})\,x + x\,\eta_\epsilon$, where $x_L(\mathbf{z})$ is a carrying volume, $\eta_\epsilon$ is centred noise with variance $\epsilon\sigma^2$, and the transition function satisfies $\Phi^\epsilon_\delta/\epsilon \to \Phi_\delta$ with

$$\Phi_\delta(y,\mathbf{z}) = \frac{\mu}{2\delta}\big(1 - y^\delta\big), \qquad y = x/x_L, \quad \mu = \mu(\mathbf{z}) \in (0,1).$$

The deterministic limit $\dot x = \Phi_\delta(x/x_L)\,x$ is of von Bertalanffy type for $-1 \le \delta < 0$ and Gompertz type as $\delta \to 0$. The volume density $f(\mathbf{z},x,t)$ obeys a Boltzmann-type kinetic equation.

**Proposition (quasi-invariant limit).** In the time scale $\tau = \epsilon t$, as $\epsilon \to 0^+$ the kinetic equation reduces to the Fokker–Planck equation with uncertainty

$$\partial_\tau f = \partial_x\Big[-\Phi_\delta(x/x_L,\mathbf{z})\,x\,f + \frac{\sigma^2}{2}\,\partial_x\big(x^2 f\big)\Big],$$

with no-flux boundary condition at $x = 0$. For each $\mathbf{z}$ it has a unique equilibrium, $f^\infty(\mathbf{z},x) \propto x^{-2}\exp\big(\int^x \frac{2\Phi_\delta(s/x_L)}{\sigma^2 s}\,ds\big)$. With $\gamma = \sigma^2/\mu(\mathbf{z})$:
1. (Gompertz, $\delta \to 0$.) $f^\infty$ is lognormal,

$$f^\infty(\mathbf{z},x) = \frac{1}{\sqrt{2\pi\gamma}\,x}\exp\Big(-\frac{(\log x - k)^2}{2\gamma}\Big), \qquad k = \log x_L - \gamma,$$

with thin, exponentially decaying tails.
2. (von Bertalanffy, $-1 \le \delta < 0$.) $f^\infty$ is an Amoroso (generalised inverse gamma) distribution,

$$f^\infty(\mathbf{z},x) = \frac{|\delta|}{\Gamma(k/|\delta|)}\frac{\theta^k}{x^{k+1}}\exp\Big(-\Big(\frac{\theta}{x}\Big)^{|\delta|}\Big), \qquad k = \frac{1}{\gamma|\delta|} + 1, \quad \theta = x_L\Big(\frac{1}{\gamma\delta^2}\Big)^{1/|\delta|},$$

with fat, polynomially decaying tails, i.e. a higher probability of very large tumours.

**Theorem (stochastic Galerkin stability).** Expanding $f$ in orthogonal polynomials of $\mathbf{z}$ up to degree $M$ gives a coupled system $\partial_\tau \hat f_k = \partial_x\big[\sum_h \mathcal{A}_{kh}\hat f_h + D(x)\,\partial_x \hat f_k\big]$. If $\|\partial_x \mathcal{A}_{kh}\|_\infty \le C_A$ for all $k,h$ and $D > 0$, then $\|\hat{\mathbf{f}}(\tau)\|_{L^2}^2 \le e^{C_A\tau}\|\hat{\mathbf{f}}(0)\|_{L^2}^2$.

## Expansion

The Fokker–Planck limit comes from a second-order Taylor expansion of test functions in the weak form, with the third-order remainder vanishing as $\epsilon \to 0$; the drift is the deterministic growth law and the diffusion $\sigma^2x^2/2$ is multiplicative because fluctuations are proportional to size. Setting the no-flux condition to zero gives a first-order ODE whose solution is the stated equilibrium; substituting $\Phi_\delta$ gives $f^\infty \propto x^{1/(\gamma\delta) - 2}\exp\big(-(x/x_L)^\delta/(\gamma\delta^2)\big)$, whose $\delta \to 0$ limit is the lognormal law and whose $\delta < 0$ case is the Amoroso law. The growth law therefore decides the tail of the tumour-size distribution, which matters for predicted risk under uncertainty. Therapy is added as a second transition $x'' = x + \epsilon S(x)u$ with a feedback control minimising $(x'' - x_d)^2 + \nu|u|^p$, which shifts the equilibrium towards a target volume $x_d$.

## Sources

- A. Medaglia, G. Colelli, L. Farina, A. Bacila, P. Bini, E. Marchioni et al., "Uncertainty quantification and control of kinetic models of tumour growth under clinical uncertainties", International Journal of Non-Linear Mechanics 141 (2022), 103933, <https://doi.org/10.1016/j.ijnonlinmec.2022.103933>. Published version of arXiv:2110.05814, cited next; locators there refer to the arXiv version.
- A. Medaglia, G. Colelli, L. Farina, A. Bacila, P. Bini, E. Marchioni, S. Figini, A. Pichiecchio, M. Zanella, "Uncertainty quantification and control of kinetic models of tumour growth under clinical uncertainties", arXiv:2110.05814 (2021), Section 2 (transition scheme, Remark 1, Fokker–Planck limit and its equilibria), Section 3 (therapeutic protocols) and Section 5 (Theorem 5.1), <https://doi.org/10.48550/arXiv.2110.05814>.
