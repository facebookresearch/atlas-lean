# Extinction threshold for infected prey in a nonautonomous eco-epidemiological model

Consider susceptible prey $S$, infected prey $I$ and predators $P$ governed by

$$S'=G(t,S)-a(t)f(S,I,P)P-\beta(t)SI,\qquad I'=\beta(t)SI-\eta(t)g(S,I,P)I-c(t)I,$$

$$P'=h(t,P)P+\gamma(t)a(t)f(S,I,P)P+\theta(t)\eta(t)g(S,I,P)I,$$

on $(\mathbb{R}_0^+)^3$, where $\beta$ is the incidence rate, $c$ the death rate of infectives, $a f$ and $\eta g$ the predation of susceptible and infected prey (general functional responses: Holling I–IV, Beddington–DeAngelis and Crowley–Martin are all included), $\gamma,\theta$ conversion rates, and $G(t,S)$, $h(t,P)P$ the vital dynamics of prey and predator. Only susceptible prey reproduce.

**Hypotheses.**
- (S1) $a,\beta,\eta,c,\gamma,\theta$ are bounded, non-negative and continuous.
- (S2) $f,g,G$ and $(t,x)\mapsto h(t,x)x$ are locally Lipschitz; $f,g\ge0$; $y\mapsto f(x,y,z)$ and $y\mapsto g(x,y,z)$ are non-increasing; $x\mapsto g(x,y,z)$ is non-increasing; $z\mapsto f(x,y,z)$ is non-increasing and $z\mapsto g(x,y,z)$ is non-decreasing.
- (S3) Solutions with positive initial data are bounded, with $\omega$-limits in a common bounded region.
- (S4) Every positive solution of the prey-only equation $s'=G(t,s)$ is bounded, bounded away from $0$, and globally attractive on $(0,\infty)$.
- (S5) Every positive solution of the predator-only equation $y'=h(t,y)y$ is bounded and globally attractive.

For positive solutions $s^*$ of $s'=G(t,s)$ and $y^*$ of $y'=h(t,y)y$, and $\lambda>0$, set

$$\mathcal{R}^u(\lambda)=\limsup_{t\to\infty}\int_t^{t+\lambda}\Big(\beta(s)s^*(s)-\eta(s)\,g\big(s^*(s),0,y^*(s)\big)-c(s)\Big)\,ds ,$$

which does not depend on the choice of $s^*,y^*$.

**Statement.** Assume (S1)–(S5), and either $G(t,S)=\Lambda(t)-\mu(t)S$ with $g(S+I,0,P)\le g(S,I,P)$, or $g$ independent of $I$. If $\mathcal{R}^u(\lambda)<0$ for some $\lambda>0$, the infected prey go extinct: $I(t)\to0$ for every solution with positive initial data.

## Expansion

Comparison gives $S\le s^*+\delta$ (infection and predation only remove susceptibles) and $P\ge y^*-\delta$ eventually. On windows of length $\lambda$ the per-capita growth of $I$ is then bounded by the integrand of $\mathcal{R}^u$ plus $O(\delta)$, which is $\le-\kappa<0$, so $\ln I$ decreases by at least $\kappa$ per window and $\liminf I=0$; a second argument rules out excursions away from $0$. In the special case $f\equiv0$, $g=P$, $G=\Lambda-\mu S$, $h=b-rP$ the threshold reduces to the one for the model of Niu, Zhang and Teng. The threshold is not sharp: it uses the disease-free, predator-free comparison solutions.

## Sources

- L. F. de Jesus, C. M. Silva and H. Vilarinho, *An eco-epidemiological model with general functional response of predator to prey*, arXiv:2001.00900 (2020), <https://doi.org/10.48550/arXiv.2001.00900>. Conditions S1)–S5) (Section 2); Proposition 1 (independence of the thresholds); Theorem 1 (extinction).
