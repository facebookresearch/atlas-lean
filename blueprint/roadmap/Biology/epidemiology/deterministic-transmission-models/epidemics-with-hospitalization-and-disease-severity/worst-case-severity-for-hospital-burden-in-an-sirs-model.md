# Worst-case severity for hospital burden in an SIRS model

**Model.** With population fractions $S,I,C,H,R$ (susceptible, standard course, critical course awaiting hospitalization, hospitalized, recovered),

$$\dot S=-\beta S(I+C)+\varepsilon R,\quad \dot I=(1-\theta)\beta S(I+C)-\gamma_II,\quad \dot C=\theta\beta S(I+C)-\gamma_CC,$$

$$\dot H=\gamma_CC-\gamma_HH,\qquad \dot R=\gamma_II+\gamma_HH-\varepsilon R,$$

where $\theta\in[0,1]$ is the probability of a severe course, hospitalized individuals do not transmit, and immunity wanes slowly, $0<\varepsilon\ll\beta,\gamma_I,\gamma_C,\gamma_H$. Assume hospitalization is faster than recovery from a standard course, $\gamma_I\le\gamma_C$. The simplex is forward invariant.

**Thresholds.** The basic reproduction number is

$$\mathcal R_0(\theta)=\beta\Big(\frac{1-\theta}{\gamma_I}+\frac{\theta}{\gamma_C}\Big),$$

decreasing in $\theta$. The disease-free equilibrium is globally asymptotically stable if $\mathcal R_0<1$ (globally exponentially stable if $\beta<\gamma_I$) and unstable if $\mathcal R_0>1$, in which case the endemic equilibrium is locally asymptotically stable. If $\gamma_I<\beta<\gamma_C$, the epidemic exists exactly for $\theta<\theta^*=\frac{1/\gamma_I-1/\beta}{1/\gamma_I-1/\gamma_C}\in(0,1)$.

**Theorem (worst-case severity).** For long times the hospitalized fraction at the endemic equilibrium is, to leading order in $\varepsilon$, proportional to $f(\theta)=\theta\,(1-1/\mathcal R_0(\theta))$, so the long-run hospitalization cost $k\int_0^tH$ is maximized by maximizing $f$. Then $\tilde\theta=1$ if $\beta\ge\gamma_C^2/\gamma_I$, while if $\beta<\gamma_C^2/\gamma_I$ (and $\beta>\gamma_I$) the maximizer is

$$\tilde\theta=\frac{\gamma_C}{\gamma_C-\gamma_I}\Big(1-\sqrt{\frac{\gamma_I}{\beta}}\Big)<1,$$

which lies in $(0,\theta^*)$ when $\gamma_I<\beta<\gamma_C$. So a more severe disease can produce fewer total hospitalizations: removing severe cases from transmission suppresses spread. If $\gamma_I=\gamma_C$, $\mathcal R_0=\beta/\gamma$ and $\tilde\theta=1$. If instead $\gamma_I>\gamma_C$, $\mathcal R_0$ increases with $\theta$ and $\tilde\theta=1$ always.

## Expansion

With $a=\beta/\gamma_I$ and $b=\beta/\gamma_C$, $\mathcal R_0=a-(a-b)\theta$ and $f'(\theta)=1-a/\mathcal R_0^2$, so the interior critical point solves $\mathcal R_0(\tilde\theta)=\sqrt a$, giving $\tilde\theta=(a-\sqrt a)/(a-b)$, which equals the stated formula and is below $1$ iff $b<\sqrt a$, i.e. $\beta<\gamma_C^2/\gamma_I$. The slow waning rate $\varepsilon$ makes the system two-timescale. Fast epidemic waves (with the constant of motion $\log S-\mathcal R_0(S+I+C)$ when $\gamma_I=\gamma_C$, giving final sizes $S_\infty\in(0,1/\mathcal R_0)$) alternate with slow replenishment of susceptibles, analyzed by geometric singular perturbation theory, including a delayed loss of stability. Simulations of the first wave show that its cost-maximizing severity is close to the equilibrium value $\tilde\theta$. The same model describes partial self-quarantine of symptomatic cases.

## Sources

- J. Borsotti, "An SIRS model with hospitalizations: economic impact by disease severity", *Chaos, Solitons & Fractals* 200 (2025), 116951, Section 2 (model, Proposition 1), Section 3 (Proposition 2, Lemma 1, Theorems 1-2, Proposition 3), Section 4 (Propositions 4-5, Lemma 2) and Section 5 (endemic-equilibrium analysis of $f(\theta)$, formulas for $\theta^*$ and $\tilde\theta$), <https://doi.org/10.1016/j.chaos.2025.116951> (preprint arXiv:2503.03540).
