# Measure-valued birth–death–mutation process of filopodia driving cell motion

**Model.** A crawling cell is treated as an overdamped active particle whose velocity balances substrate friction against unit pulling forces of its adherent filopodia: if the filopodia at time $t$ have orientations $\theta_1,\dots,\theta_{N_t}\in[0,2\pi)$, encoded by the point measure $\nu_t=\sum_{i=1}^{N_t}\delta_{\theta_i}$, then

$$
\gamma\,\vec V_t=\begin{pmatrix}\langle\nu_t,\cos\rangle\\ \langle\nu_t,\sin\rangle\end{pmatrix},\qquad \langle\nu,f\rangle=\int f\,d\nu .
$$

The filopodial population evolves as a structured population with four events: isotropic creation at total rate $c$ (orientation uniform); death of each filopodium at rate $d$; reproduction of a filopodium of orientation $\theta$ at rate $r(\theta,\nu)$, producing an exact copy with probability $1-\mu$ or, with probability $\mu$, a new filopodium with orientation drawn from a kernel $g(z;\theta)$ centred at $\theta$. Polarization enters through the reproduction rate, e.g. $r(\theta,\nu)=r^*\,f(\theta;\vec V)$ with $f$ the von Mises density centred at $\arg\vec V$ with concentration $\kappa(\|\vec V\|)$ nondecreasing in speed, so faster cells reinforce protrusion in their direction of motion.

**Proposition (existence, uniqueness, moment bound).** Write the process as the solution of a stochastic differential equation driven by independent Poisson point measures (one per event type, thinned by indicator functions to the state-dependent rates). Assume the reproduction rate is bounded, $0\le r(\theta,\nu)\le\bar r$, and $\mathbb E[N_0]<\infty$. Then there is a solution $\nu\in\mathbb D(\mathbb R_+,\mathcal M)$ (càdlàg paths in finite point measures on the circle), pathwise uniqueness holds, and for every $T>0$

$$
\mathbb E\Big[\sup_{t\le T}N_t\Big]\le\mathbb E[N_0]\,e^{\bar rT}+\frac c{\bar r}\big(e^{\bar rT}-1\big)<\infty .
$$

**Proposition (Markov property).** The solution is a Markov process with infinitesimal generator, for bounded measurable $\Phi$,

$$
\begin{aligned}
L\Phi(\nu)={}&\int\frac c{2\pi}\big[\Phi(\nu+\delta_\theta)-\Phi(\nu)\big]d\theta+\int(1-\mu)\,r(\theta,\nu)\big[\Phi(\nu+\delta_\theta)-\Phi(\nu)\big]\nu(d\theta)\\
&+\int\mu\,r(\theta,\nu)\int\big[\Phi(\nu+\delta_z)-\Phi(\nu)\big]g(z;\theta)\,dz\,\nu(d\theta)+\int d\,\big[\Phi(\nu-\delta_\theta)-\Phi(\nu)\big]\nu(d\theta).
\end{aligned}
$$

In particular its law does not depend on the auxiliary ordering used to label individuals.

## Expansion

The total jump rate is at most $c+(\bar r+d)N_t$, so jump times can be defined recursively. Dropping deaths and taking expectations up to the stopping times $\tau_n=\inf\{t:N_t\ge n\}$ gives $\mathbb E[\sup_{s\le t\wedge\tau_n}N_s]\le\mathbb E[N_0]+cT+\bar r\int_0^t\mathbb E[\sup_{u\le s\wedge\tau_n}N_u]\,ds$; Gronwall yields the bound, which forces $\tau_n\to\infty$ and excludes explosion, and Fatou removes the localization. Uniqueness holds because jump times and marks are determined pathwise by the driving measures. Without interaction ($r$ constant), $N_t$ is a linear immigration–birth–death process; with velocity feedback the branching property is lost. Simulated trajectories range from Brownian-like to persistent as the polarization strength increases, and a higher mutation probability lowers territory exploration.

## Proof depends on

- [Gronwall inequality in integral form](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- C. Etchegaray, N. Meunier, "A stochastic model for protrusion activity" (2018), Section 2 (model) and Section 3, Propositions 3.3 and 3.4. <https://doi.org/10.48550/arXiv.1808.00217>
