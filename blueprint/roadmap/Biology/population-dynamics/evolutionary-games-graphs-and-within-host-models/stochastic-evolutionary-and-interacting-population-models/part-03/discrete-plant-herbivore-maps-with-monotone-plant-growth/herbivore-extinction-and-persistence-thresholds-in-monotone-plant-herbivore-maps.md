# Herbivore extinction and persistence thresholds in monotone plant–herbivore maps

**Model.** Let $P_t$ be edible plant biomass and $H_t$ herbivore density in generation $t$, and let $F(P)=Pf(P)$ be the plant growth map with per capita rate $f$. With attack parameter $a>0$, consider

$$
\text{Model I:}\quad P_{t+1}=F(P_t)e^{-aH_t},\quad H_{t+1}=P_t\big(1-e^{-aH_t}\big);\qquad
\text{Model II:}\quad P_{t+1}=F(P_t)e^{-aH_t},\quad H_{t+1}=F(P_t)\big(1-e^{-aH_t}\big),
$$

where Model I has herbivores attacking before plant growth and Model II after it. Hypotheses on the plant map:

- **H1:** $F(0)=0$, $F(P)>0$ and $F'(P)>0$ for $P>0$, and $F(P)\to C>0$ as $P\to\infty$ (monotone, contest-type growth);
- **H2:** $f\ge 0$, $f'<0$ and $f(P)\to 0$ as $P\to\infty$ (scramble-type per capita decline).

Under H1, let $0=\bar P^0<\bar P^1<\dots<\bar P^n$ be the non-degenerate fixed points of $F$; they alternate in stability and the largest one $\bar P^n$ is stable and attracts the plant dynamics from above.

**Theorem.** Assume H1 for Models I and II.

1. *(Dissipativity.)* $\limsup_{t\to\infty}\max\{P_t,H_t\}\le\bar P^n$.
2. *(Herbivore extinction.)* If $a\bar P^n<1$, then $H_t\to 0$ and every solution is attracted to the plant-only dynamics; if moreover $F'(0)<1$ and $(0,0)$ is the only boundary equilibrium, $(0,0)$ is globally stable.
3. *(Uniform persistence.)* Assume in addition **H3:** the smallest positive fixed point satisfies $a\bar P^1>1$ and $f(0)>1$. Then both models are uniformly persistent with respect to the open quadrant: there is $\epsilon>0$ with $\liminf_{t\to\infty}\min\{P_t,H_t\}\ge\epsilon$ for every initial condition with $P_0H_0>0$.

The boundary equilibria are $(0,0)$ and $(\bar P^i,0)$; in both models the Jacobian at $(\bar P^i,0)$ has eigenvalues $F'(\bar P^i)$ and $a\bar P^i$, so $a\bar P^i$ is the herbivore invasion number at the plant state $\bar P^i$.

## Expansion

Since $1-e^{-aH}\le aH$, the herbivore satisfies $H_{t+1}\le a(\bar P^n+\epsilon)H_t$ eventually, a geometric contraction when $a\bar P^n<1$: herbivores die out if they attack too weakly or if the plant cannot sustain enough biomass. Persistence uses average Lyapunov functions: $L=P$ near the plant-free set, where $P_t/P_0\approx f(0)^t$ grows because $f(0)>1$, and $L=H$ near the plant-only fixed points, where $H_t/H_0\approx(a\bar P^i)^t$ grows because H3 gives $a\bar P^i\ge a\bar P^1>1$ for all $i$. The two thresholds coincide when the plant map has a single positive fixed point $\bar P^1$: the herbivore dies out for $a\bar P^1<1$ and persists for $a\bar P^1>1$.

## Sources

- Y. Kang, D. Armbruster, *Noise and seasonal effects on the dynamics of plant-herbivore models with monotonic plant growth functions*, arXiv:1102.2279 (2011). <https://doi.org/10.48550/arXiv.1102.2279> — Proposition 2.1 (single-plant dynamics), Lemma 4.1 (dissipativity), Theorem 4.2 (herbivore extinction), Theorem 4.5 (uniform persistence), Section 4. Published version: International Journal of Biomathematics 04(03) (2011), 255–274, <https://doi.org/10.1142/s1793524511001234>; locators above refer to the arXiv version.
