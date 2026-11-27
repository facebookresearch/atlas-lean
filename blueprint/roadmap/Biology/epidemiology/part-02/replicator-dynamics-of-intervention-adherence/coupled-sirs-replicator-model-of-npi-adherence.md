# Coupled SIRS–replicator model of NPI adherence

**Model.** In a population of constant size, $S, I, R = 1 - S - I$ are susceptible, infected and recovered fractions and $x \in [0,1]$ is the fraction adhering to a symmetric non-pharmaceutical intervention (NPI) that multiplies transmission by $p \in (0,1)$ whenever either party adheres. With transmission rate $\beta$, recovery $\gamma$, birth and death rate $\mu$, waning immunity $\delta$, perceived risk of infection $\xi > 0$ and adherence cost $c > 0$, the payoffs of non-adherers and adherers are

$$\pi_N = -\beta I \xi (1 - x) - p \beta I \xi x, \qquad \pi_A = p\, \pi_N - c,$$

and

$$\begin{aligned}
\dot S &= \mu - b(x)\beta S I - \mu S + \delta(1 - S - I),\\
\dot I &= b(x)\beta S I - (\gamma + \mu) I,\\
\dot x &= x(1 - x)(\pi_A - \pi_N), \qquad b(x) = p x + (1 - x).
\end{aligned}$$

The adherence equation is the two-strategy replicator equation for the fitnesses $(\pi_N, \pi_A)$, since $x(\pi_A - \bar\pi) = x(1-x)(\pi_A - \pi_N)$ for the mean payoff $\bar\pi = x\pi_A + (1-x)\pi_N$. Let $\mathcal{R}_0 = \beta/(\gamma + \mu)$.

**Equilibria and stability.**

1. Disease-free equilibria $(S, I, x) = (1, 0, 0)$ and $(1, 0, 1)$. The first is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$; the second is always unstable (adherence is costly when there is no infection).
2. Endemic equilibria with no or full adherence: $x = 0$, $S^* = 1/\mathcal{R}_0$, $I^* = \frac{\mu + \delta}{\mu + \delta + \gamma}\big(1 - \frac{1}{\mathcal{R}_0}\big)$; and $x = 1$, $S^* = 1/(p\mathcal{R}_0)$, $I^* = \frac{\mu + \delta}{\mu + \delta + \gamma}\big(1 - \frac{1}{p\mathcal{R}_0}\big)$, the latter existing only if $p\mathcal{R}_0 > 1$.
3. A partial-adherence endemic equilibrium with

$$I^*_m = \frac{\mu + \delta}{(1-p)(\gamma + \mu)(\mu + \delta)\,\xi/c + \gamma + \mu + \delta}, \qquad S^*_m = \frac{(1-p)(\gamma+\mu)\,\xi}{c}\, I^*_m, \qquad x^*_m = \frac{1}{1-p}\Big(1 - \frac{\gamma + \mu}{\beta S^*_m}\Big),$$

which exists iff $0 < x^*_m < 1$. All three quantities depend on $c$ and $\xi$ only through the cost-to-risk ratio $c/\xi$. Whenever it exists it is locally stable, and the no- and full-adherence endemic equilibria are then unstable. In particular, if $\mathcal{R}_0 > 1$, no adherence is stable exactly when $c/\xi \ge (\mathcal{R}_0 - 1)(1-p)(\gamma+\mu)(\mu+\delta)/(\gamma+\mu+\delta)$, i.e. when $x^*_m \le 0$.

**With vaccination** (fraction $q$ of births vaccinated, susceptibles vaccinated at rate $\nu$), the disease-free susceptible fraction becomes $S^0 = \frac{\mu(1-q) + \delta}{\mu + \nu + \delta}$ and the reproduction number $\mathcal{R}_0(\nu) = \mathcal{R}_0 S^0$, with analogous endemic equilibria in which $\mu + \delta$ is replaced by $\mu(1-q) + \delta$ in the infected fractions.

## Depends on

- [Solution of the replicator equation](../../../population-dynamics/replicator-dynamics/is-solution.md)

## Expansion

Adherers gain from adherence only by lowering their own infection risk: $\pi_A - \pi_N = (1-p)\xi\, b(x)\beta I - c$, so adherence spreads when the expected reduction in perceived infection loss exceeds its cost. At an interior equilibrium this payoff difference vanishes, $(1-p)\xi\, b\beta I = c$, while $b\beta S = \gamma + \mu$ and the $S$-equation give $\mu + \delta = (\mu + \delta)S + (\gamma + \mu + \delta)I$; solving these three equations gives the formulas for $I^*_m, S^*_m, x^*_m$. The replicator equation here is the payoff-difference-linear social learning rule of [replicator equation](../../../population-dynamics/replicator-dynamics/is-solution.md). The model shows a tension across scales: vaccination lowers prevalence and hence the incentive to adhere, so equilibrium adherence can fall as vaccination rises, partially offsetting its benefit.

## Sources

- C. M. Saad-Roy, A. Traulsen, "Dynamics in a behavioral–epidemiological model for individual adherence to a nonpharmaceutical intervention", Proceedings of the National Academy of Sciences USA 120 (2023) e2311584120, Model (equations [2]–[3]), Materials and Methods A (equilibria [4]–[6], Theorems 1–2 of the SI Appendix) and B (vaccination model [7]–[10], Theorem 3), <https://doi.org/10.1073/pnas.2311584120>.
