# Global stabilization of an age-structured chemostat

Consider the age-structured chemostat with cell density $f(t,a)$, substrate $S(t)$ and dilution $D(t) > 0$,

$$ \partial_t f + \partial_a f = -(\beta(a) + D) f, \qquad f(t,0) = \mu(S)\int_0^\infty k(a) f(t,a)\, da, \qquad \dot S = D(S_{\mathrm{in}} - S) - \mu(S)\int_0^\infty q(a) f(t,a)\, da , $$

with bounded $C^1$ functions $\mu, \beta, k, q \ge 0$, where $\mu(0) = 0$ and $\mu(S) > 0$ for $S > 0$, and solutions satisfy $f(t,a) \to 0$ as $a \to \infty$ for every $t \ge 0$. Assume (B): there are constants $b, \gamma \ge 0$ and $p_0, q_0 > 0$ with $\beta \le b$ and

$$ q(a) = q_0\, e^{\int_0^a \beta(s)\,ds - b a}, \qquad k(a) = (p_0 + \gamma q_0 a)\, e^{\int_0^a \beta(s)\,ds - b a} . $$

Then the feed activity $X = \int q f\,da$ and birth activity $Y = \int k f\,da$ obey the closed system

$$ \dot S = D(S_{\mathrm{in}}-S) - \mu(S) X, \qquad \dot X = q_0\mu(S) Y - (b + D) X, \qquad \dot Y = p_0 \mu(S) Y + \gamma X - (b+D) Y , $$

whose equilibria for $D \equiv D^*$ satisfy $\mu(S^*) = (b+D^*)^2/(p_0(b+D^*) + \gamma q_0)$. Let $\lambda = 1 - p_0\mu(S^*)/(b + D^*) \in [0,1)$.

Assume (C): there is a constant $\phi > 1$ such that for all $S \in [S^*, S_{\mathrm{in}}]$

$$ \Big(b - \frac{\lambda(b+D^*)}{2}\Big)\Big(\frac{\mu(S^*)}{\mu(S)} - 1\Big) + (1+\lambda)\frac{\lambda^2\phi(b+D^*)^2}{4D^*}\Big(\frac{\mu(S^*)}{\mu(S)} - 1\Big)^2 < D^*\Big(1 - \frac{1}{4(1+\lambda)\phi}\Big) $$

(the source's (30)); when $\gamma = 0$, so $\lambda = 0$, it is equivalent to $p_0\mu(S) > b$ on $[S^*, S_{\mathrm{in}}]$.

**Theorem.** Under (B) and (C), for every $\delta > 0$ and $\alpha \in [0,1)$ the feedback

$$ D(X,S) = \frac{D^*\mu(S)X}{\mu(S^*)X^*} + \frac{\delta}{\mu(S^*)^{1+\alpha}}\, \big|\mu(S)-\mu(S^*)\big|^{1+\alpha}\, \mathbf{1}_{\{S\le S^*\}} $$

globally asymptotically stabilizes $(X^*, Y^*, S^*)$ on $(0,\infty)^2\times(0,S_{\mathrm{in}})$, and locally exponentially if $\alpha > 0$ and $\lambda > 0$. The feedback does not use the birth activity $Y$.

## Depends on

- [Global feedback stabilization of the chemostat with mortality](global-feedback-stabilization-of-the-chemostat-with-mortality.md)

## Expansion

Differentiating $X$ and $Y$ along the McKendrick equation and using the boundary condition produces terms $\int (q' - \beta q) f$ and $\int(k' - \beta k) f$; the exponential forms in (B) make these equal to $-bX$ and $\gamma X - bY$, which closes the moments into a three-dimensional ODE. Logarithmic coordinates map the open state space onto $\mathbb{R}^3$, and a control Lyapunov function analogous to the lumped case, with an extra term for the ratio $Y/X$, yields global attractivity under (C).

## Sources

- Iasson Karafyllis, Epiphane Loko, Miroslav Krstić, Antoine Chaillet, "Global stabilisation of chemostats with nonzero mortality and substrate dynamics", International Journal of Control 99 (2026), 3122–3142, <https://doi.org/10.1080/00207179.2026.2713102>. Published version of arXiv:2502.09310, cited next; locators there refer to the arXiv version.
- I. Karafyllis, E. Loko, M. Krstic, A. Chaillet, "Global Stabilization of Chemostats with Nonzero Mortality and Substrate Dynamics", arXiv:2502.09310 (2025), Section 3 (age-structured chemostat; assumptions (B) and (C), equilibria and Theorem 3) and Section 5.3 (proof of Theorem 3). <https://doi.org/10.48550/arXiv.2502.09310>
