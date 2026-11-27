# Well-posedness and boundary equilibria of the bee–Varroa–virus model

**Model.** Let $B$ and $I$ be healthy and virus-infected bees, $M$ and $N$ virus-free and virus-carrying mites. With all parameters positive,

$$B' = b\frac{B}{B+I} - \lambda BN - \gamma BI - mB, \qquad I' = b\frac{I}{B+I} + \lambda BN + \gamma BI - (m+\mu)I,$$

$$M' = r(M+N) - nM - \frac{p}{h(B+I)}M(M+N) - M(\beta I + \delta N + eB),$$

$$N' = -nN - \frac{p}{h(B+I)}N(N+M) + \beta MI + \delta MN - eNB,$$

on $\mathcal D^0 = \{(B,I,M,N) \in \mathbb R^4_+ : B + I \ne 0\}$. Here $b$ is the queen's daily laying rate, split between healthy and infected brood in proportion to the colony composition; $\lambda$ and $\gamma$ are mite-to-bee and bee-to-bee transmission rates; $m$ and $\mu$ are natural and disease-induced bee mortality; $r$, $n$ are mite birth and death rates; $p/(h(B+I))$ is mite crowding relative to the number of hosts; $\beta$ is acquisition of the virus by mites from infected bees, $\delta$ mite-to-mite transmission, and $e$ the grooming removal of mites by healthy bees.

**Theorem (well-posedness and boundedness).** For $X_0 \in \mathcal D^0$ there is a unique solution on $[0,\infty)$; it stays in $\mathcal D^0$, and, with $\tilde m = m + \mu$ and some constant $L > 0$,

$$\frac{b}{\tilde m} \le \liminf_{t\to\infty}(B + I) \le \limsup_{t\to\infty}(B + I) \le \frac bm, \qquad M(t) + N(t) \le L \quad (t \ge 0).$$

**Boundary equilibria.**

- $E_1 = (b/m, 0, 0, 0)$ (healthy, mite-free colony) and $E_2 = (0, b/(m+\mu), 0, 0)$ (fully infected, mite-free) always exist.
- $E_3 = \big(b/m, 0, M_3, 0\big)$ with $M_3 = (r - n - eb/m)\,hb/(pm)$ (healthy bees with virus-free mites) is feasible iff $r - n > eb/m$: mites persist only if their birth rate beats their death rate plus grooming by the healthy population.
- $E_4 = \Big(\dfrac{\mu^2 - b\gamma + m\mu}{\mu\gamma}, \dfrac{b\gamma - m\mu}{\mu\gamma}, 0, 0\Big)$ (endemic virus without mites) is feasible iff $0 < b\gamma - m\mu < \mu^2$.
- A healthy-bee-free equilibrium $E_5 = (0, b/(m+\mu), M_5, N_5)$ arises from the intersection in the positive quadrant of two conics in the $(M,N)$ plane; a coexistence equilibrium is studied numerically.

## Expansion

The vector field is locally Lipschitz on $\mathcal D^0$. Adding the bee equations gives $(B+I)' = b - m(B+I) - \mu I$, squeezed between $b - \tilde m(B+I)$ and $b - m(B+I)$, which yields the two-sided bound and shows that $B + I$ cannot reach $0$. Adding the mite equations, the crowding term $-p(M+N)^2/(h(B+I))$ dominates the linear growth $r(M+N)$ once $B + I$ is bounded above, giving the uniform bound on mites. The equilibria follow by setting the right-hand side to zero on each coordinate face: on $I = N = 0$, $B = b/m$ the mite equation reduces to the logistic law $M' = M\big(r - n - eb/m - pmM/(hb)\big)$, with grooming loss $eB$, and on $M = N = 0$ the bee subsystem is an SI model with proportional birth.

## Sources

- SARA BERNARDI, EZIO VENTURINO, "An epidemiological model of viral infections in a Varroa-infested bee colony: the case of a bee-dependent mite population size", in Mathematical Biology and Biological Physics (2017), 165–186, <https://doi.org/10.1142/9789813227880_0010>. Published version of arXiv:1609.04314, cited next; locators there refer to the arXiv version.
- Sara Bernardi, Ezio Venturino, "An epidemiological model of viral infections in a Varroa-infested bee colony: the case of a bee-dependent mite population size", arXiv (2016). Model section, Theorem (well-posedness and boundedness), Section "Equilibria". <https://doi.org/10.48550/arXiv.1609.04314>
