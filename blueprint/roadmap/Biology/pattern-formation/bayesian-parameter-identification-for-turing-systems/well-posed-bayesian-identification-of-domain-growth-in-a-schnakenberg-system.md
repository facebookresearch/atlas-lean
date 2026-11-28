# Well-posed Bayesian identification of domain growth in a Schnakenberg system

**Forward model.** A bounded domain $\Omega_t \subset \mathbb R^m$ ($m = 1, 2$) grows uniformly and isotropically, $x(t) = \rho(t)\, x(0)$ with $\rho \in C^1$, $\rho(0) = 1$, $\rho > 0$. Mapping back to the initial domain $\Omega_0$, the concentrations $u, v$ satisfy

$$\begin{aligned}
u_t + m\frac{\dot\rho(t)}{\rho(t)}\, u &= \frac{1}{\rho(t)^2}\, \Delta u + \gamma f(u, v), \\
v_t + m\frac{\dot\rho(t)}{\rho(t)}\, v &= \frac{d}{\rho(t)^2}\, \Delta v + \gamma g(u, v),
\end{aligned} \qquad x \in \Omega_0,$$

with zero-flux boundary conditions, non-negative bounded initial data, and Schnakenberg (activator-depleted) kinetics

$$f(u, v) = a - u + u^2 v, \qquad g(u, v) = b - u^2 v,$$

where $d$ is the diffusion ratio and $\gamma$ the scale parameter. The dilution term $m\dot\rho/\rho$ and the $\rho^{-2}$ factor on diffusion come from mass conservation on the moving domain.

**Bayesian inverse problem.** Let $p$ be the unknown parameter in a separable Banach space $U$ with prior $P_0$, $\mathcal G : U \to Y$ the observation operator (parameter to observed pattern), and data $y = \mathcal G(p) + \eta$ with Gaussian noise $\eta \sim N(0, \Sigma)$, so the potential is $\Phi(p; y) = \|y - \mathcal G(p)\|_\Sigma^2$ (up to the conventional factor).

- *Bayes' theorem.* If $\Phi$ is measurable and $Z = \int_U \exp(-\Phi(p; y))\, P_0(dp) > 0$, the posterior $P^y$ exists, is absolutely continuous with respect to $P_0$, and $\dfrac{dP^y}{dP_0}(p) = \dfrac{1}{Z} \exp(-\Phi(p; y))$.
- *Well-posedness.* If (i) for every $\varepsilon > 0$ there is $M$ with $\|\mathcal G(p)\|_\Sigma \le \exp(\varepsilon \|p\|_U^2 + M)$ for all $p$, and (ii) $\mathcal G$ is Lipschitz on bounded sets, then $P^y$ exists and depends continuously on $y$.

**Proposition.** For the growing-domain Schnakenberg system with $a, b, d, \gamma > 0$, the problem of identifying the growth function $\rho$ (with $\rho(0) = 1$ and final size known) satisfies conditions (i)–(ii), so the parameter identification problem is well-posed. The same framework identifies kinetic and diffusion parameters $(a, b, d, \gamma)$ on stationary domains.

## Depends on

- [Schnakenberg reaction kinetics](../turing-patterns-and-diffusion-driven-instability/schnakenberg.md)

## Expansion

Writing the posterior as a reweighting of the prior avoids Lebesgue densities, which do not exist on infinite-dimensional parameter spaces; this matters because the growth function $\rho$ is a function of time and its discretizations should approximate a meaningful limit object. Condition (i) is supplied by a priori estimates for the growing-domain system, which bound the $L^2$ norm of the solution by the square of the $L^2$ norm of the growth, and condition (ii) by continuous dependence of solutions on $\rho$; positivity of solutions keeps the kinetics in their admissible range. Numerically, the posterior is explored by Markov chain Monte Carlo after discretizing the parameter, with each likelihood evaluation requiring a finite-element solve of the reaction-diffusion system; posterior marginals reveal which parameters a Turing pattern actually constrains.

## Sources

- E. Campillo-Funollet, C. Venkataraman, A. Madzvamuse, "Bayesian Parameter Identification for Turing Systems on Stationary and Evolving Domains", Bulletin of Mathematical Biology (2019), Theorem 1 (Bayes' theorem in infinite dimensions), Proposition 1 (well-posedness), the growing-domain reaction-diffusion system (Eqs. 3–4) and Proposition 2. <https://doi.org/10.1007/s11538-018-0518-z> (PMC6320356).
