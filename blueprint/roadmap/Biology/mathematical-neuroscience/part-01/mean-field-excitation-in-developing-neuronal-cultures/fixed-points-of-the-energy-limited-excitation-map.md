# Fixed points of the energy-limited excitation map

Extend the mean-field excitation map by an energy-like resource $E_t$ that limits activation:

$$q_{t+1} = 1 - \left(1 - p\,\sigma(E_t, \underline{E})\right)^{z q_t},\qquad E_{t+1} = (1-\varepsilon)E_t + \varepsilon\bar E - r q_t\,H(E_t - r q_t),$$

where $\sigma(E, \underline{E}) = \tfrac12\left(\tanh(wE - \underline{E}) + 1\right)$, $H$ is the Heaviside function, $p \in (0,1)$ is the maximal activation probability, $z > 0$ the coordination number, $r > 0$ the energy cost of activation, $w, \underline{E} > 0$ set the activation threshold, $\bar E > \underline{E}$ is the recovery level and $\varepsilon \in (0,1)$ the relaxation rate.

**Proposition.** The domain $\{(q, E) : q \in [0,1],\ E \in [0,\bar E]\}$ is forward invariant, and, writing $\kappa = -z\log\!\left(1 - p\,\sigma(\bar E, \underline{E})\right)$:

1. if $\kappa \le 1$, the only fixed point is $(q_1^*, E_1^*) = (0, \bar E)$, and it is an attractor when $\kappa < 1$;
2. if $\kappa > 1$ and $\bar E / r \ge 1$, there are at most two fixed points: $(0, \bar E)$, which is a repeller, and possibly one further fixed point $(q_2^*, E_2^*)$ specified by $0 < q_2^* \le \bar E/\bigl(r(1 + 1/\varepsilon)\bigr)$, $q_2^* < 1$, $q_2^* = 1 - \bigl(1 - p\,\sigma(\bar E - r q_2^*/\varepsilon, \underline{E})\bigr)^{q_2^* z}$ and $E_2^* = \bar E - r q_2^*/\varepsilon$ (source Eq. (6));
3. if $\kappa > 1$ and $\bar E / r < 1$, there are at most three fixed points: $(0, \bar E)$, a repeller; possibly $(q_2^*, E_2^*)$ specified by Eq. (6) as in item 2; and possibly $(q_3^*, \bar E)$ with $1 > q_3^* > \bar E / r$ solving $q_3^* = 1 - \left(1 - p\,\sigma(\bar E, \underline{E})\right)^{z q_3^*}$, which, if it exists, is a stable attractor.

Despite this simple equilibrium structure, the map produces bursts, periodic and irregular activity resembling recordings from developing neuronal cultures.

## Depends on

- [Threshold for self-sustained activity in the mean-field excitation map](threshold-for-self-sustained-activity-in-the-mean-field-excitation-map.md)

## Expansion

At the rest state the energy recovers to $\bar E$, so the linearization in $q$ is the basic excitation map with activation probability $p\,\sigma(\bar E, \underline{E})$, and the threshold $\kappa = 1$ plays the role of $-z\log(1-p) = 1$. When activity is high enough that $r q > E$, the Heaviside switch stops the energy drain, so fixed points with $E = \bar E$ and $q > \bar E/r$ solve the basic excitation equation with the reduced probability $p\,\sigma(\bar E, \underline{E})$. Below that level, energy depletion and activation balance at the intermediate fixed point.

## Sources

- I. Y. Tyukin, D. Iudin, F. Iudin, T. Tyukina, V. Kazantsev, I. Mukhina and A. N. Gorban, "Simple model of complex dynamics of activity patterns in developing networks of neuronal cultures", *PLOS ONE* 14 (2019), e0218304, section "Mean-field dynamic model of neuronal excitation", Eq. (4) and Proposition 2, Eqs. (5)–(7), proved in the Appendix. <https://doi.org/10.1371/journal.pone.0218304> (PMC6597067)
