# Random attractor and extinction in a predator–prey model with prey disease under bounded noise

**Model.** Let $(\Omega,\mathcal F,\mathbb P,\theta)$ be a metric dynamical system and consider susceptible prey $S$, infected prey $I$ and predators $P$ with random recruitment:

$$S'=\Lambda(\theta_t\omega)-\mu S-f(S,I,P)P-\beta SI,$$

$$I'=\beta SI-\eta\,g(S,I,P)I-cI,$$

$$P'=\gamma f(S,I,P)P+r\eta\,g(S,I,P)I-\delta_1P-\delta_2P^2.$$

Hypotheses: all rates are positive with $\mu<c$; the predation responses $f,g\ge0$ are locally Lipschitz, $f$ nondecreasing in $S$ and nonincreasing in $I,P$, $g$ nondecreasing in $P$ and nonincreasing in $S,I$, $f(0,I,P)=0$, $g(S,I,0)=0$ and $f(S,0,0)>0$ for $S>0$ (covering Holling I–IV, Beddington–DeAngelis and Crowley–Martin responses); the recruitment is real (bounded) noise, $\Lambda(\theta_t\omega)\in[\Lambda^\ell,\Lambda^u]=q_0[1-\epsilon,1+\epsilon]$ with $\epsilon\in(0,1)$, continuous in $t$. Set $a^u=\max\{\gamma,r\}$ and $\Theta^u=a^u\Lambda^u/\min\{\mu,\delta_1\}$.

**Theorem.**

*(1)* For every $\omega$ and nonnegative initial data there is a unique bounded nonnegative solution, generating a random dynamical system, and this system has a unique global random attractor $\mathcal A$; deterministic invariant regions of the form $\mathcal K_\delta$ serve as absorbing sets.

*(2)* (Prevalence of susceptible prey.) With $\xi_\delta=\Lambda^\ell-f\big(\tfrac{\Theta^u+\delta}{a^u},0,0\big)(\Theta^u+\delta)$ and $\zeta_\delta=\mu+\beta\tfrac{\Theta^u+\delta}{r}$, the $S$-component of every section satisfies $A_S(\omega)\ge\xi_\delta/\zeta_\delta$; in particular susceptibles are prevalent if $\xi_\delta>0$ for some $\delta>0$.

*(3)* (Joint extinction of infection and predators.) If

$$\frac{\beta\,\Theta^u}{a^u}<c\qquad\text{and}\qquad\gamma f\Big(\frac{\Theta^u}{a^u},0,0\Big)<\delta_1,$$

then the attractor has singleton sections $\mathcal A(\omega)=(S^*(\omega),0,0)$.

For the sub-model without predators (random SI model) the attractor is deterministic, $A_S(\omega)\ge\Lambda^\ell/(\mu+\beta\Lambda^u/\mu)$, and the infection dies out, $\mathcal A_{SI}(\omega)=(S^*(\omega),0)$, whenever $\beta\Lambda^u/\mu<c$.

## Expansion

Bounded noise makes the problem a random ODE solved pathwise. Weighted total populations ($N=\gamma S+\dots$ type combinations with coefficients between $a^\ell=\min\{\gamma,r\}$ and $a^u$) obey linear differential inequalities with constant bounds, so their limits lie in $[\Theta^\ell,\Theta^u]$ and give compact, positively invariant absorbing sets; a compact absorbing set yields a unique pullback attractor. On the attractor $S\le\Theta^u/a^u$, so the infected class decays when $\beta\Theta^u/a^u<c$, and the predator then decays when even maximal prey availability gives conversion $\gamma f(\Theta^u/a^u,0,0)$ below the death rate $\delta_1$.

## Sources

- Lopo F. de Jesus, César M. Silva, Helder Vilarinho, "Random perturbations of an eco-epidemiological model", arXiv:2007.10188 (2020), Theorems 1–4, Propositions 2–5 and 8–9, <https://doi.org/10.48550/arXiv.2007.10188>.
