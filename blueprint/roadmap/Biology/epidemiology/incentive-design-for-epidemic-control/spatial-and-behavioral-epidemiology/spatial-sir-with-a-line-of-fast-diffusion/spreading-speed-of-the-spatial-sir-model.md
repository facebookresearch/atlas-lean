# Spreading speed of the spatial SIR model with immobile susceptibles

Let $S(t, X)$ and $I(t, X)$, $X \in \mathbb{R}^2$, be the densities of susceptible and infected individuals in

$$\partial_t I - d\,\Delta I + \alpha I = \beta S I, \qquad \partial_t S = -\beta S I, \qquad t > 0,$$

with diffusivity $d > 0$ of infected individuals, removal rate $\alpha > 0$, transmission rate $\beta > 0$, uniform initial susceptibles $S(0, \cdot) \equiv S_0 > 0$, and a nonnegative, compactly supported initial infection $I(0, \cdot) = I_0 \not\equiv 0$. Put

$$R_0 = \frac{S_0 \beta}{\alpha}, \qquad f(v) = S_0 (1 - e^{-\beta v}) - \alpha v.$$

**Reduction (Berestycki, Roquejoffre and Rossi 2020, Eqs. 3–5).** The cumulative infection $v(t, X) = \int_0^t I(s, X)\, ds$ satisfies $S(t, X) = S_0 e^{-\beta v(t, X)}$ and solves the Fisher–KPP equation with a source,

$$\partial_t v - d\,\Delta v = f(v) + I_0(X), \qquad v(0, \cdot) \equiv 0.$$

The nonlinearity $f$ is concave with $f(0) = 0$ and $f'(0) = \alpha (R_0 - 1)$.

**Theorem (Berestycki, Roquejoffre and Rossi 2020, Theorem 3.3).** Assume $R_0 > 1$ and set

$$c_{\mathrm{SIR}} = 2\sqrt{d\, \alpha (R_0 - 1)}.$$

Let $v_\infty$ be the unique positive bounded stationary solution of $-d \Delta v = f(v) + I_0$ (its limit at infinity is the positive zero $v^*$ of $f$). Then for every $\varepsilon \in (0, c_{\mathrm{SIR}})$,

$$\lim_{t \to \infty} \max_{|X| \le (c_{\mathrm{SIR}} - \varepsilon) t} |v(t, X) - v_\infty(X)| = 0, \qquad \lim_{t \to \infty} \max_{|X| \ge (c_{\mathrm{SIR}} + \varepsilon) t} v(t, X) = 0.$$

So the epidemic invades the plane at asymptotic speed $c_{\mathrm{SIR}} = 2\sqrt{d f'(0)}$, and the final fraction infected far from the epicentre is $1 - e^{-\beta v^*}$.

## Depends on

- [Kolmogorov–Petrovsky–Piskunov: fronts exist at every speed $c \ge 2\sqrt{rD}$](../../../../pattern-formation/fisher-kpp-travelling-waves/exists-is-front-of-le.md)
- [Final-size relation (Kermack–McKendrick 1927)](../../../kermack-mckendrick-sir-model/final-size.md)

## Expansion

Dividing $\partial_t S = -\beta S I$ by $S$ and integrating gives $\ln(S/S_0) = -\beta v$. Adding the two equations and integrating in time gives $\partial_t v - d \Delta v + \alpha v = S_0 - S + I_0 = S_0(1 - e^{-\beta v}) + I_0$, the stated KPP equation. Because $I_0$ has compact support it does not affect the far field, where the dynamics is that of $\partial_t v = d \Delta v + f(v)$ with KPP nonlinearity; the classical Aronson–Weinberger spreading theorem then gives speed $2\sqrt{d f'(0)}$, while the stationary problem governs the behaviour on compact sets.

## Sources

- H. Berestycki, J.-M. Roquejoffre and L. Rossi, "Propagation of Epidemics Along Lines with Fast Diffusion", Bulletin of Mathematical Biology 83 (2021), 2, Section 3.1 (Eqs. 3–6, Theorem 3.3), <https://doi.org/10.1007/s11538-020-00826-8> (PMC7734393).
