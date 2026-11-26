# Critical community size of the SIR model with vital dynamics

**Model.** In a closed population of constant size $N$ with birth and death rate $\mu$, infection rate $\beta$ and recovery rate $\gamma$, the susceptible and infected densities $s=S/N$, $y=Y/N$ satisfy

$$
s'=-\beta sy+\mu(1-s),\qquad y'=\beta sy-(\mu+\gamma)y,
$$

with $R_0=\beta/(\gamma+\mu)$. For $R_0>1$ every solution with $y(0)>0$ converges, through damped oscillations, to the endemic equilibrium $s^*=1/R_0$, $y^*=\frac{\mu}{\gamma+\mu}\bigl(1-\frac1{R_0}\bigr)$. Start the epidemic with one infective: $s(0)=1-\frac1N$, $y(0)=\frac1N$.

**Proposition (monotone extrema, Appendix A).** Along a solution, the successive local minima of $y(t)$ form an increasing sequence and the successive local maxima a decreasing sequence. Hence the first local minimum of $y$ for $t>0$, if it exists, is its global minimum on $(0,\infty)$.

**Definitions.** The disease **fades out** if $y(t^*)=1/N$ with $y'(t^*)<0$ at some $t^*>0$, i.e. the infected count drops below one individual. Let $\Psi(\beta,\gamma,\mu,N)$ be the first local minimum of $y$ for $t>0$ (and $\Psi=y^*$ if $y$ has no local minimum). With $\beta,\gamma,\mu$ fixed, $\tilde N$ is the **deterministic critical community size** if

$$
\Psi(\beta,\gamma,\mu,\tilde N)=\frac{1}{\tilde N}.
$$

**Consequence.** For populations smaller than $\tilde N$ the infection fades out after the first outbreak, and for populations of size at least $\tilde N$ it persists and $y\to y^*$. The value $\tilde N$ is not a function of $R_0$ alone: level curves of $\tilde N$ in the $(\gamma,\beta)$ plane accumulate near $R_0=1$ for large clearance rates. Adding this extinction rule to a two-strain SIR model breaks the competitive exclusion principle: a strain with larger $R_0$ can be driven out by one with smaller $R_0$ if its post-outbreak trough falls below $1/N$.

## Depends on

- [Kermack–McKendrick SIR model](../kermack-mckendrick-sir-model/README.md)

## Expansion

Starting near the disease-free state with $R_0>1$, $y$ first grows into an outbreak that depletes susceptibles below $1/R_0$, after which $y$ decays to a trough while births replenish $s$; the trough depth is extremely small when $\mu$ is small, since recovery is fast relative to demographic replenishment. Monotonicity of the extrema (the system has a Lyapunov function $V=s-s^*\ln s+y-y^*\ln y$ that decreases along orbits, so successive oscillations shrink toward the equilibrium) makes the first trough decisive. Treating densities below one individual as extinction ($y\mapsto0$ once $Ny<1$) yields the threshold $\Psi=1/\tilde N$, computed numerically by integrating to the first minimum and bisecting in $N$. (The source writes the endemic infected density with $\beta$ in place of $\gamma$ in the denominator; solving $\mu(1-s^*)=\beta s^*y^*$ gives the expression above.)

## Sources

- M. Ferreira dos Santos and C. Castilho, "Deterministic critical community size for the SIR system and viral strain selection", arXiv:2004.14920 (2020), Section 2 (normalized SIR system, definitions of fade out, $\Psi$ and the critical community size), Section 3 (two-strain competition) and Appendix A (monotonicity of extrema), <https://doi.org/10.48550/arXiv.2004.14920>.
