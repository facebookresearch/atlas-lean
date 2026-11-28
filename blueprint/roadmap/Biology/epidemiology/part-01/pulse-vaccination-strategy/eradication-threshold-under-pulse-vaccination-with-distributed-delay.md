# Eradication threshold under pulse vaccination with distributed delay

**Impulsive linear lemma.** For $a, b > 0$ and $0 < \theta < 1$, the impulsive system $\dot u = a - bu$ for $t \ne k\tau$, $u(k\tau^+) = (1-\theta)u(k\tau)$, has a unique positive $\tau$-periodic solution

$$\tilde u_e(t) = \frac{a}{b} + \Big(u^\ast - \frac{a}{b}\Big)e^{-b(t - k\tau)}, \quad k\tau < t \le (k+1)\tau, \qquad u^\ast = \frac{a}{b}\cdot\frac{(1-\theta)(1 - e^{-b\tau})}{1 - (1-\theta)e^{-b\tau}},$$

and it is globally asymptotically stable.

**Model.** Time is scaled so that infecteds leave at rate $1$; $\mu$ is the birth and death rate, $R_0$ the basic reproduction number, $f \ge 0$ a probability density on $[0, h]$ describing the delay between infection and infectiousness (survival $e^{-\mu s}$), and a fraction $\theta \in (0,1)$ of susceptibles is vaccinated every $\tau$ time units:

$$\dot S = \mu - R_0\int_0^h f(s) S(t-s) I(t-s) e^{-\mu s}ds - \mu S, \qquad \dot I = R_0\int_0^h f(s) S(t-s) I(t-s) e^{-\mu s}ds - I, \qquad t \ne k\tau,$$

$$S(k\tau^+) = (1 - \theta) S(k\tau), \qquad I(k\tau^+) = I(k\tau).$$

Without infection, $S$ converges to the periodic solution $\tilde S_e(t) = 1 - \dfrac{\theta\, e^{-\mu(t - k\tau)}}{1 - (1-\theta)e^{-\mu\tau}}$ on $(k\tau, (k+1)\tau]$.

**Theorem.** Let

$$R^\ast = R_0\,\frac{1 - e^{-\mu\tau}}{1 - (1-\theta)e^{-\mu\tau}}, \qquad R_\ast = (1-\theta)\,e^{-\mu h}\, R^\ast .$$

1. If $R^\ast < 1$, the infection-free periodic solution $(\tilde S_e, 0)$ is globally attractive. In particular this holds for any $R_0 \le 1$, and for $R_0 > 1$ whenever $\theta > \theta^\ast = (R_0 - 1)(e^{\mu\tau} - 1)$ or $\tau < \tau_\ast = \frac{1}{\mu}\ln\big(1 + \frac{\theta}{R_0 - 1}\big)$.
2. If $R_\ast > 1$, the disease is uniformly persistent: there is $q > 0$ with $I(t) \ge q$ for all large $t$; if moreover $\mu > R_0$ the system is permanent.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The lemma follows from the stroboscopic map $u((k+1)\tau) = (1-\theta)\big[a/b + (u(k\tau) - a/b)e^{-b\tau}\big]$, an affine map with slope $(1-\theta)e^{-b\tau} < 1$, whose fixed point $u^\ast$ is globally attracting. For eradication, $S$ is dominated by the solution of the infection-free impulsive equation, so eventually $S(t) \le \tilde S_e(t) + \epsilon$, whose maximum, attained just before each pulse, is $(1 - e^{-\mu\tau})/(1 - (1-\theta)e^{-\mu\tau})$, so that $R^\ast = R_0 \max_t \tilde S_e(t)$; then $I$ satisfies a linear distributed-delay inequality $\dot I \le -I + R_0'\int_0^h f(s) I(t-s)\,ds$ with $R_0' = R_0(\max\tilde S_e + \epsilon) < 1$, which forces $I \to 0$ by the Beretta–Takeuchi stability criterion for $\dot y = -a_1 y + a_2\int_0^h f(s)y(t-s)ds$ ($y = 0$ is globally asymptotically stable iff $a_2 < a_1$), and $S \to \tilde S_e$ follows. Persistence uses the lower bound $(1-\theta)$ on the post-pulse susceptible fraction and the delay survival $e^{-\mu h}$, which is why $R_\ast < R^\ast$ and a gap remains between the two thresholds; the sharp threshold is the spectral radius of the period map of the linearized delay equation along $\tilde S_e$. Larger pulses or shorter inter-pulse periods favour eradication.

## Sources

- S. Gao, Z. Teng, J. J. Nieto and A. Torres, "Analysis of an SIR epidemic model with pulse vaccination and distributed time delay", Journal of Biomedicine and Biotechnology 2007 (2007), 64870, Sections 2–3 (Lemmas 1–2, Eqs. (10)–(26), Theorems 1–3, Corollaries 1–5), <https://doi.org/10.1155/2007/64870>, PMCID: PMC2217597.
