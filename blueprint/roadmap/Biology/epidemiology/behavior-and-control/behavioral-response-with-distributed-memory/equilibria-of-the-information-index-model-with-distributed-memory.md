# Equilibria of the information-index model with distributed memory

**Model.** Early in an outbreak (negligible susceptible depletion) prevalence $I$ and the behavior-modulated transmission rate $\beta$ satisfy the renewal-type delay system

$$I'(t) = \beta(t)I(t) - \gamma I(t), \qquad \beta(t) = f\Bigl(\int_0^\infty g\bigl(\beta(t-s)I(t-s)\bigr)K(s)\,ds\Bigr),$$

where $g$ (message function) is increasing with $g(0) = 0$ and converts new cases $\beta I$ into information; the memory kernel $K \ge 0$ with $\int_0^\infty K = 1$ weights past information, for example the delay from infection to diagnosis; $f$ is decreasing, giving the transmission rate as a function of perceived risk, with $\beta_0 = f(0)$; and $\gamma > 0$ is the recovery rate. Set $R_0 = \beta_0/\gamma$.

**Equilibria.** Besides the disease-free equilibrium $E_0 = (0, \beta_0)$, there is the endemic equilibrium

$$E_+ = \Bigl(\frac{g^{-1}\bigl(f^{-1}(\gamma)\bigr)}{\gamma},\ \gamma\Bigr),$$

which exists and is positive iff $R_0 > 1$. Both equilibria are independent of the kernel $K$.

**Proposition.** Take the gamma memory kernel

$$K(s) = \frac{\mu^\alpha s^{\alpha-1}e^{-\mu s}}{\Gamma(\alpha)}, \qquad s \ge 0,\ \alpha, \mu > 0$$

(mean delay $\alpha/\mu$), and pose the system on history spaces weighted by $w(\theta) = e^{\rho\theta}$, $\theta \le 0$, with $\rho > 0$ ($wI_t$ continuous and vanishing at $-\infty$, $\beta_t$ integrable against $w$), so that stability is decided by the characteristic roots with $\Re\lambda > -\rho$. If $\rho < \mu$, then $E_0$ is locally asymptotically stable when $R_0 < 1$ and unstable when $R_0 > 1$, for every such gamma kernel: its characteristic equation is $\lambda + \gamma - \beta_0 = 0$.

The kernel matters for $E_+$: the source finds, analytically for selected kernels and numerically in general, that the endemic equilibrium can lose stability as the memory kernel varies, producing sustained, behavior-induced epidemic waves. Pseudospectral approximation of the delay equation by ODEs, which extends the linear chain trick beyond Erlang kernels, makes these bifurcations numerically computable.

## Expansion

At equilibrium the information index equals $g(\beta^* I^*)$ and must make $f$ return exactly $\gamma$, so $\beta^* = \gamma$ and $I^* = g^{-1}(f^{-1}(\gamma))/\gamma$; this requires $\gamma$ to be in the range of $f$ below $\beta_0$, i.e. $R_0 > 1$. Near $E_0$, information vanishes to first order because $g(0) = 0$, so the linearization is just $I' = (\beta_0 - \gamma)I$, independent of $K$. At $E_+$ the feedback loop "cases, delayed information, reduced contacts, fewer cases" is a delayed negative feedback, and delayed negative feedback oscillates once the delay is long or concentrated enough.

## Sources

- A. Andò, S. De Reggi, F. Scarabel, R. Vermiglio, "Behavior-induced oscillations in epidemic outbreaks with distributed memory: beyond the linear chain trick using numerical methods", *Mathematical Biosciences and Engineering* 23(1) (2026), 76–96, system (2.1), kernel (2.3), weight (2.4), the equilibrium equations of Section 3 and Proposition 3.1, <https://doi.org/10.3934/mbe.2026004> (preprint arXiv:2511.21199).
