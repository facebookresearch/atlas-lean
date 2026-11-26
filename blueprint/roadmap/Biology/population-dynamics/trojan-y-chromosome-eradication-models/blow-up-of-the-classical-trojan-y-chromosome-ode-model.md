# Blow-up of the classical Trojan Y-chromosome ODE model

**Model.** Let $f$, $m$, $s$ be adult females, wild-type males and YY supermales, released at constant rate $\mu \ge 0$. With birth rate $\beta$, death rate $\delta$, carrying capacity $K$ and logistic factor $L = 1 - (f + m + s)/K$,

$$\dot f = \tfrac12\beta L fm - \delta f, \qquad \dot m = \tfrac12\beta L fm + \beta L fs - \delta m, \qquad \dot s = \mu - \delta s.$$

Female-male matings produce daughters and sons in equal proportion; female-supermale matings produce only (XY) sons.

**Lemma 1 (loss of positivity).** There exist positive initial data $(f_0, m_0, s_0)$ and a time interval $[T_1, T_2] \subset (0,\infty)$ on which the male population $m(t)$ is negative.

**Theorem 2.1 (blow-up without releases).** If $\mu = 0$, there exist sufficiently large positive initial data for which the solution blows up in finite time: $\limsup_{t \to T^*} f(t) = +\infty$ or $\limsup_{t \to T^{**}} m(t) = -\infty$ for some finite $T^*$ or $T^{**}$.

**Theorem 2.2 (blow-up driven by releases).** If $\mu > 0$, then for every positive initial datum there is a critical release rate $\mu^*(f_0, m_0, s_0)$ such that for every $\mu > \mu^*$ the solution blows up in finite time in the same sense.

The model is therefore not well posed as a population model, which motivated modified formulations (a separate logistic factor for supermale matings, female mate choice, male-supermale competition, pair-formation models) whose non-negative solutions exist globally and still drive the wild type to extinction.

## Expansion

Heuristically, the defect sits in the factor $L$: once $f + m + s > K$, $L$ is negative and the mating terms reverse sign. Large supermale numbers make $\beta L fs$ a strong negative drain on $m$ that is not proportional to $m$, so $m$ can cross zero; after that, $\tfrac12\beta L fm$ becomes positive in the female equation (both $L$ and $m$ negative), and the quadratic term in $f$ can drive a finite-time explosion of $f$, with $m$ escaping to $-\infty$. Releasing supermales faster pushes the total above $K$ sooner, which is why every initial condition blows up once $\mu$ is large enough.

## Sources

- D. K. Mallawa Arachchi, R. D. Parshad, C. Kadelka, "Invasive species control via a discrete model for the Trojan Y-chromosome strategy" (2025), Section 2 (classical model, Lemma 1 and Theorems 2.1 and 2.2, restating earlier results of Takyi and coauthors), <https://doi.org/10.48550/arXiv.2506.14023>.
