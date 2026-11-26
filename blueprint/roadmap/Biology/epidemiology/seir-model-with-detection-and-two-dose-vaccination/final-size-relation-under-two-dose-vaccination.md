# Final-size relation for an SEIR epidemic with a finite two-dose vaccination campaign

**Model.** In a closed population of size $N$, let $\rho \in (0,1)$ be the fraction of infectives that are detected and isolated (only undetected infectives transmit), $\beta$ the contact rate, $1/\sigma$ the incubation time and $\gamma$ the removal rate. Susceptibles receive first doses at rate $\Delta_1(t)$ and second doses at rate $\Delta_2(t)$ per day, with efficacies $\pi_1 \le \pi_2$:

$$\begin{aligned} \dot S &= -\frac{\beta}{N} (1-\rho) S I - \frac{S}{N}\bigl(\pi_1 \Delta_1(t) + (\pi_2 - \pi_1)\Delta_2(t)\bigr), & \dot E &= \frac{\beta}{N}(1-\rho) S I - \sigma E, \\ \dot I &= \sigma E - \gamma I, \qquad \dot R = \gamma I, & \dot V &= \frac{S}{N}\bigl(\pi_1 \Delta_1(t) + (\pi_2 - \pi_1)\Delta_2(t)\bigr). \end{aligned}$$

Assume $\Delta_i(t) \to 0$ and that the total numbers of doses $\bar\Delta_i = \int_0^\infty \Delta_i(t)\, dt$ are finite.

**Proposition.** For nonnegative initial data the solution stays nonnegative and converges to an equilibrium $(S_\infty, 0, 0, N - S_\infty - V_\infty, V_\infty)$ of the limiting (vaccination-free) system. If $S(0) = S_0 > 0$ and $R(0) = R_0$, the limits satisfy

$$\frac{\beta (1-\rho)}{\gamma N}\bigl(S_\infty + V_\infty\bigr) - \log S_\infty = \frac{1}{N}\bigl(\pi_1 \bar\Delta_1 + (\pi_2 - \pi_1)\bar\Delta_2\bigr) + \frac{\beta(1-\rho)}{\gamma N}(N - R_0) - \log S_0 .$$

The vaccination campaign enters the final-size relation only through the effective number of protected people $\pi_1 \bar\Delta_1 + (\pi_2 - \pi_1)\bar\Delta_2$, and detection acts by scaling the transmission rate to $\beta(1-\rho)$.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Since $W = S + E + I + V$ satisfies $\dot W = -\gamma I$, integrating gives $\gamma \int_0^\infty I\, dt = N - R_0 - S_\infty - V_\infty$. Dividing the $S$ equation by $S$ and integrating gives $\log S_\infty - \log S_0 = -\frac{\beta(1-\rho)}{N}\int_0^\infty I\, dt - \frac{1}{N}\bigl(\pi_1 \bar\Delta_1 + (\pi_2 - \pi_1)\bar\Delta_2\bigr)$; eliminating $\int I$ yields the relation. Convergence follows because $S$ and $S + V$ are monotone, $I$ is integrable, and $E$ cannot stay bounded away from zero without $E + I$ eventually becoming negative. With no vaccination this is the classical Kermack–McKendrick final-size equation.

## Sources

- José Luis Sainz-Pardo, José Valero, "Optimizing COVID-19 vaccine distribution adding spatio-temporal criteria", arXiv (2023). Lemma 1, Lemma 2, Lemma 3 (Section 3). <https://doi.org/10.48550/arXiv.2311.18122>
