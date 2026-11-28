# Equilibria and locust invasion in the crop–locust–pesticide model

**Model.** Let $C$ and $M$ be premature and mature crop biomass, $L$ locust density and $P$ pesticide concentration, with positive parameters: crop growth rate $r$, carrying capacity $K$, maturation rate $\sigma < r$, harvest rate $hE$, consumption rate $\beta$, conversion efficiency $\xi$, locust self-limitation $\mu$, pesticide kill coefficient $\varphi\gamma$, spray rate $\theta$ and pesticide depletion rate $\theta_0$:

$$\dot C = rC\Big(1 - \frac{C+M}{K}\Big) - \sigma C - \beta CL,\qquad \dot M = \sigma C\Big(1 - \frac{C+M}{K}\Big) - hEM - \beta ML,$$

$$\dot L = \xi\beta(M+C)L - \varphi\gamma PL - \mu L^2,\qquad \dot P = \theta L - \theta_0 P .$$

**Equilibria.**

1. $E_0 = (0,0,0,0)$, unstable since its Jacobian has the eigenvalue $r - \sigma > 0$.
2. The locust-free equilibrium

    $$E_1 = \Big(\frac{hEK(r-\sigma)}{hEr + \sigma^2},\ \frac{K\sigma^2(r-\sigma)}{r(hEr+\sigma^2)},\ 0,\ 0\Big),$$

    with total crop $C+M = K(r-\sigma)/r$. It is always unstable: the locust direction has eigenvalue $\xi\beta K(r-\sigma)/r > 0$, so locusts invade any locust-free crop.

3. The coexistence equilibrium $E_2 = (C^*, M^*, L^*, P^*)$ with

    $$L^* = \frac{\beta\theta_0K\xi(r-\sigma)}{\beta^2\theta_0K\xi + \gamma\theta r\varphi + \theta_0\mu r},\qquad P^* = \frac{\theta}{\theta_0}L^*,\qquad C^* + M^* = \frac{K}{r}(r - \sigma - \beta L^*),$$

    which is positive whenever $r > \sigma$; its local stability is decided by the Routh–Hurwitz conditions on the quartic characteristic polynomial of the Jacobian.

## Expansion

With $L = 0$, $\dot C = 0$ gives $C + M = K(r-\sigma)/r$ and $\dot M = 0$ then gives $M = \sigma^2C/(rhE)$, which yields $E_1$. At $E_1$ the per-capita locust growth rate is $\xi\beta(C+M) = \xi\beta K(r-\sigma)/r$, positive because locusts face no density-independent mortality in the model. At $E_2$, eliminating $C + M$ and $P$ from $\dot C = \dot L = \dot P = 0$ gives a linear equation for $L^*$. The Jacobian entry $2\mu L^* + \gamma\varphi P^* - \beta\xi(C^* + M^*)$ in the locust row equals $\mu L^*$ by the equilibrium relation $\xi\beta(C^*+M^*) = \varphi\gamma P^* + \mu L^*$, so it is automatically positive at $E_2$. Pesticide spraying lowers $L^*$ through the term $\gamma\theta r\varphi$ in the denominator.

## Depends on

- [Logistic growth](../../../logistic-growth-equation/logistic.md)

## Sources

- Mamo DK, Bedane DS, "Modelling the effect of desert locust infestation on crop production with intervention measures", Heliyon (2021), Section 2, Eq. (1); Section 3, Eqs. (3)–(11) and Theorems 1–3, <https://doi.org/10.1016/j.heliyon.2021.e07685>, PMCID PMC8342970.
