# Uniform strong persistence of infected prey in a nonautonomous eco-epidemiological model

For the nonautonomous susceptible prey–infected prey–predator model

$$S'=G(t,S)-a(t)f(S,I,P)P-\beta(t)SI,\quad I'=\beta(t)SI-\eta(t)g(S,I,P)I-c(t)I,\quad P'=h(t,P)P+\gamma(t)a(t)f(S,I,P)P+\theta(t)\eta(t)g(S,I,P)I,$$

with general functional responses $f,g$, assume the regularity, monotonicity and boundedness conditions (S1)–(S3) of the extinction threshold, together with condition (S6) on the *uninfected subsystem*

$$x'=G(t,x)-a(t)f(x,0,z)z,\qquad z'=h(t,z)z+\gamma(t)a(t)f(x,0,z)z :$$

there are two families of perturbed versions of this subsystem, indexed by small $\varepsilon\ge0$ (perturbations $G_{1,\varepsilon}\le G\le G_{2,\varepsilon}$, $h_{1,\varepsilon}\le h\le h_{2,\varepsilon}$, plus terms of size $v(\varepsilon)\rho(t)$ with $0<\rho^\ell\le\rho\le\rho^u$ and $v(0)=0$, $v'$ bounded between positive constants near $0$), each having a globally asymptotically stable non-negative solution $(x^*_{1,\varepsilon},z^*_{1,\varepsilon})$, respectively $(x^*_{2,\varepsilon},z^*_{2,\varepsilon})$, depending continuously on $\varepsilon$ in the sup norm. Write $x_1^*=x^*_{1,0}$ and $z_2^*=z^*_{2,0}$ and set

$$\mathcal{R}^\ell(\lambda)=\liminf_{t\to\infty}\int_t^{t+\lambda}\Big(\beta(s)x_1^*(s)-\eta(s)\,g\big(x_1^*(s),0,z_2^*(s)\big)-c(s)\Big)\,ds ,$$

which is independent of the chosen solutions.

**Statement.** If $\mathcal{R}^\ell(\lambda)>0$ for some $\lambda>0$, the infected prey are uniformly strongly persistent: there are $0<m_1<m_2$ such that every solution with positive initial data satisfies $m_1<\liminf_{t\to\infty}I(t)\le\limsup_{t\to\infty}I(t)<m_2$.

In the periodic case, with all coefficients $\omega$-periodic, both $\mathcal{R}^\ell$ and $\mathcal{R}^u$ (for $\lambda=\omega$) are averages over one period, so the two theorems give explicit invasion criteria computed from the disease-free predator–prey dynamics.

## Expansion

First one shows weak persistence, $\limsup I\ge v(\varepsilon)\rho^\ell/[(1+\beta^u)(1+\theta^u\eta^u)]$: if $I$ stayed below this level, the $(S,P)$ dynamics would be squeezed between the two perturbed uninfected subsystems, so $S\ge x_1^*-\delta$ and $P\le z_2^*+\delta$ eventually, and the windowed growth rate of $\ln I$ would be at least $\kappa>0$, a contradiction. Uniform strong persistence then follows from weak persistence and the boundedness in (S3) by the standard argument for dissipative nonautonomous systems. Examples covered include Gause-type and ratio-dependent uninfected subsystems.

## Depends on

- [Extinction threshold for infected prey in a nonautonomous eco-epidemiological model](extinction-threshold-for-infected-prey-in-a-nonautonomous-eco-epidemiological-model.md)

## Sources

- L. F. de Jesus, C. M. Silva and H. Vilarinho, *An eco-epidemiological model with general functional response of predator to prey*, arXiv:2001.00900 (2020), <https://doi.org/10.48550/arXiv.2001.00900>. Condition S6) (Section 2); Theorem 2 (uniform strong persistence); Section 3 (examples).
