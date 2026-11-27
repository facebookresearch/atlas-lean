# Reproduction number and final-size relation of the SIDARTHE model

With $r_1 = \varepsilon + \zeta + \lambda$, $r_2 = \eta + \rho$, $r_3 = \theta + \mu + \kappa$, $r_4 = \nu + \xi$, the basic reproduction number of the SIDARTHE model is the reciprocal of the susceptible threshold,

$$R_0 = \frac{1}{\bar S^{*}} = \frac{\alpha}{r_1} + \frac{\beta \varepsilon}{r_1 r_2} + \frac{\gamma \zeta}{r_1 r_3} + \frac{\delta \eta \varepsilon}{r_1 r_2 r_4} + \frac{\delta \zeta \theta}{r_1 r_3 r_4},$$

and the equilibrium is stable exactly when $\bar S R_0 < 1$; at the outset $\bar S \approx 1$, so the threshold reduces to $R_0 < 1$. For positive initial conditions the limits $\bar S$, $\bar H$, $\bar E$ satisfy

$$f_0 + R_0\big(S(0) - \bar S\big) = \log\frac{S(0)}{\bar S}, \qquad \bar H = H(0) + f_H + R_H\big(S(0) - \bar S\big), \qquad \bar E = E(0) + f_E + R_E\big(S(0)-\bar S\big),$$

with $f_0 = -c^\top F^{-1} x(0)$, $f_H = -f^\top F^{-1} x(0)$, $f_E = -d^\top F^{-1} x(0)$, $R_H = -f^\top F^{-1} b$, $R_E = -d^\top F^{-1} b$, where $f^\top = [\lambda\ \rho\ \kappa\ \xi\ \sigma]$ and $d^\top = [0\ 0\ 0\ 0\ \tau]$. If only undetected infected are present initially, $f_0 = R_0 I(0)$.

## Depends on

- [Stability threshold of the infected subsystem](stability-threshold-of-the-idart-subsystem.md)

## Proof sketch

Each term of $R_0$ is a product of the probability of reaching a compartment and the transmission rate of that compartment divided by its exit rate: $\alpha/r_1$ counts transmissions while undetected and asymptomatic, $\beta\varepsilon/(r_1 r_2)$ those made after detection, and so on, so $R_0 = -c^\top F^{-1} b = G(0)$ is the static gain of the infected subsystem, the next-generation quantity for this chain. The final-size relation comes from integrating $\dot S/S = -y_S$ to get $\int_0^\infty y_S = \log(S(0)/\bar S)$, integrating $\dot x$ over $[0,\infty)$ with $x(\infty) = 0$ to get $-x(0) = F\int_0^\infty x - b(\bar S - S(0))$, and premultiplying by $c^\top F^{-1}$. The same premultiplication by $f^\top$ or $d^\top$ yields the healed and deceased limits. The relation holds for constant parameters; after a policy change at time $t_0$, it must be restarted from $x(t_0)$ and $S(t_0)$ with the new matrix $F$.

## Sources

- Giordano G, Blanchini F, Bruno R, et al. Modelling the COVID-19 epidemic and implementation of population-wide interventions in Italy. *Nature Medicine* 26:855-860 (2020), Methods, equations (18)-(23), Proposition 3. DOI <https://doi.org/10.1038/s41591-020-0883-7>. PMCID PMC7175834.
