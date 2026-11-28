# Unique interior equilibrium of monotone plant–herbivore maps

**Model.** Let $P_t$ be edible plant biomass and $H_t$ herbivore density in generation $t$, and let $F(P)=Pf(P)$ be the plant growth map with per capita rate $f$. With attack parameter $a>0$, consider

$$
\text{Model I:}\quad P_{t+1}=F(P_t)e^{-aH_t},\quad H_{t+1}=P_t\big(1-e^{-aH_t}\big);\qquad
\text{Model II:}\quad P_{t+1}=F(P_t)e^{-aH_t},\quad H_{t+1}=F(P_t)\big(1-e^{-aH_t}\big),
$$

where Model I has herbivores attacking before plant growth and Model II after it. Hypotheses on the plant map:

- **H1:** $F(0)=0$, $F(P)>0$ and $F'(P)>0$ for $P>0$, and $F(P)\to C>0$ as $P\to\infty$ (monotone, contest-type growth);
- **H2:** $f\ge 0$, $f'<0$ and $f(P)\to 0$ as $P\to\infty$ (scramble-type per capita decline).

Under H1, let $0=\bar P^0<\bar P^1<\dots<\bar P^n$ be the non-degenerate fixed points of $F$; they alternate in stability and the largest one $\bar P^n$ is stable and attracts the plant dynamics from above.

**Theorem.**

1. *(Model I.)* If H1 and H2 hold, Model I has at most one interior equilibrium, namely the crossing in the open quadrant of the decreasing nullcline $P=f^{-1}(e^{aH})$ and the increasing nullcline $P=H/(1-e^{-aH})$. Since these start at $P=f^{-1}(1)=\bar P^1$ and $P=1/a$ when $H=0$, one exists when $a\bar P^1>1$ (the source states this condition with a misprint, as $f^{-1}(0)>1/a$).
2. *(Model II.)* If H1 holds, Model II has at most one interior equilibrium, which exists when $F^{-1}(1/a)<1/a$; it lies on the intersection of the decreasing nullcline $P=H/(e^{aH}-1)$ and the increasing nullcline $P=F^{-1}\big(H/(1-e^{-aH})\big)$.
3. *(Transcritical origin.)* In both models the interior equilibrium emerges generically through a transcritical bifurcation from the largest plant-only equilibrium $(\bar P^n,0)$ when $a\bar P^n=1$.

## Expansion

At an interior equilibrium of Model II, $P=F(P)e^{-aH}$ and $H=F(P)(1-e^{-aH})$ give $F(P)=H/(1-e^{-aH})$ and $P=H/(e^{aH}-1)$. Under H1 the first relation defines an increasing function of $H$ with minimum $F^{-1}(1/a)$ at $H=0$, while the second is decreasing with maximum $1/a$ at $H=0$, so the curves cross at most once and do cross when $F^{-1}(1/a)<1/a$. At $(\bar P^n,0)$ the Jacobian is upper triangular with eigenvalues $F'(\bar P^n)<1$ and $a\bar P^n$; as $a$ increases through $1/\bar P^n$ the second eigenvalue crosses $1$ with nonzero speed $\bar P^n$, and its eigenvector points into the positive quadrant, so a branch of interior equilibria bifurcates from the plant-only state. Monotone plant growth therefore gives at most one coexistence state, in contrast with non-monotone (Ricker-type) plant growth, for which the source's simulations show bistability.

## Depends on

- [Herbivore extinction and persistence thresholds in monotone plant–herbivore maps](herbivore-extinction-and-persistence-thresholds-in-monotone-plant-herbivore-maps.md)

## Sources

- Y. Kang, D. Armbruster, *Noise and seasonal effects on the dynamics of plant-herbivore models with monotonic plant growth functions*, arXiv:1102.2279 (2011). <https://doi.org/10.48550/arXiv.1102.2279> — Theorem 4.3 (Section 4.2, unique interior equilibrium and transcritical bifurcation). Published version: International Journal of Biomathematics 04(03) (2011), 255–274, <https://doi.org/10.1142/s1793524511001234>; locators above refer to the arXiv version.
