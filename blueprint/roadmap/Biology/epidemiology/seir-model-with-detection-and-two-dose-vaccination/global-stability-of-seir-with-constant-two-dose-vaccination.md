# Threshold global stability of the SEIR model with constant two-dose vaccination and vital dynamics

**Model.** With equal birth and death rates $\mu > 0$ (so the population stays at $N$), detection fraction $\rho \in (0,1)$, contact rate $\beta$, incubation rate $\sigma$, removal rate $\gamma$, and constant daily doses $\Delta_1, \Delta_2$ with efficacies $\pi_1, \pi_2$, set $p = \pi_1 \Delta_1 + (\pi_2 - \pi_1)\Delta_2$ and consider

$$\begin{aligned} \dot S &= \mu N - \frac{\beta}{N}(1-\rho) S I - \frac{p}{N} S - \mu S, & \dot E &= \frac{\beta}{N}(1-\rho) S I - (\sigma + \mu) E, \\ \dot I &= \sigma E - (\gamma + \mu) I, \qquad \dot R = \gamma I - \mu R, & \dot V &= \frac{p}{N} S - \mu V. \end{aligned}$$

Define the reproduction number

$$\mathcal{R}_0 = \frac{\mu N \sigma \beta (1-\rho)}{(\sigma + \mu)(\gamma + \mu)(p + \mu N)} .$$

There is always the disease-free equilibrium $P^* = \bigl(\frac{\mu N^2}{p + \mu N}, 0, 0, 0, \frac{p N}{p + \mu N}\bigr)$, and an endemic equilibrium $P^e$ with $S^e = \frac{(\sigma+\mu)(\gamma+\mu) N}{\sigma \beta (1-\rho)}$, $I^e = \frac{\mu N^2 - S^e (p + \mu N)}{\beta(1-\rho) S^e}$, $E^e = \frac{\gamma+\mu}{\sigma} I^e$, $R^e = \frac{\gamma}{\mu} I^e$, $V^e = \frac{p}{\mu N} S^e$ exists if and only if $\mathcal{R}_0 > 1$.

**Theorem.**

1. If $\mathcal{R}_0 < 1$, $P^*$ is locally and globally asymptotically stable in the feasible region.
2. If $\mathcal{R}_0 > 1$, $P^e$ is locally asymptotically stable, and every solution with $E(0) + I(0) > 0$ (initial $(S,E,I)$ in the interior of the invariant region) converges to $P^e$.

Vaccination lowers $\mathcal{R}_0$ through the factor $\mu N/(p + \mu N)$; eradication requires $p > \mu N \bigl(\frac{\sigma \beta (1-\rho)}{(\sigma+\mu)(\gamma+\mu)} - 1\bigr)$.

## Depends on

- [Final-size relation for an SEIR epidemic with a finite two-dose vaccination campaign](final-size-relation-under-two-dose-vaccination.md)

## Expansion

The $(S, E, I)$ subsystem decouples. Local stability follows from the Jacobians (Routh–Hurwitz at $P^e$). For $\mathcal{R}_0 < 1$ a Lyapunov function of Volterra type in $S$ plus a linear combination of $E$ and $I$ has derivative $-\frac{(\mu N^2 - S(p+\mu N))^2}{S N (p + \mu N)} + \frac{(\sigma+\mu)(\gamma+\mu)}{\sigma}(\mathcal{R}_0 - 1) I \le 0$, and LaSalle's invariance principle gives convergence to $P^*$. For $\mathcal{R}_0 > 1$ the system is competitive in a suitable orthant order and uniformly persistent: the disease-free equilibrium is the only $\omega$-limit point on the boundary and cannot attract interior orbits. A Poincaré–Bendixson-type theorem for three-dimensional competitive systems then says interior $\omega$-limit sets are closed orbits or the endemic equilibrium, and any periodic orbit would be orbitally asymptotically stable, which is excluded via the second additive compound matrix of the Jacobian, giving global convergence to $P^e$; $R$ and $V$ follow by linear asymptotics.

## Sources

- José Luis Sainz-Pardo, José Valero, "Optimizing COVID-19 vaccine distribution adding spatio-temporal criteria", arXiv (2023). Lemma 4, Theorem 5, Theorem 6, Theorem 7, Lemma 8, Lemma 9, Theorem 10, Theorem 11, Theorem 12, Theorem 13 (Section 4). <https://doi.org/10.48550/arXiv.2311.18122>
