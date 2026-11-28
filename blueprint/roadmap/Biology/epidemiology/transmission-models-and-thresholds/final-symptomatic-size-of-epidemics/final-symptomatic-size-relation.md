# Final symptomatic size relation

In a closed epidemic where infected individuals may or may not develop symptoms, the **final symptomatic size** $\pi_{\mathrm{sym}}$ is the limiting fraction of the population that is ever infected and shows symptoms. Let the "infection event" be the biological one (entry into the infected class), let $R_0$ be the corresponding basic reproduction number, and let susceptibility levels be constant in time.

**Homogeneous population.** If all individuals are equivalent and $p_{\mathrm{sym}}$ is the probability that a case ever becomes symptomatic, then the final size $\pi$ is the unique positive root of $\pi = 1 - e^{-R_0 \pi}$ (for $R_0 > 1$) and

$$\pi_{\mathrm{sym}} = p_{\mathrm{sym}}\, \pi .$$

Hence $\pi_{\mathrm{sym}}$ is increasing in both $R_0$ and $p_{\mathrm{sym}}$.

**Age-of-infection example.** For the model in which asymptomatic cases $i(t, \tau)$ are structured by age of infection $\tau \in [0, T]$ with infectivity $\beta_1(\tau)$ and recovery rate $\gamma_1(\tau)$, become symptomatic at age $T$ with probability $p$, and symptomatic cases transmit at rate $\beta_2$ and recover at rate $\gamma_2$, write $\Gamma_1(\tau) = \exp\left(\int_0^\tau \gamma_1(s)\, ds\right)$. Then

$$R_0 = \int_0^T \frac{\beta_1(\tau)}{\Gamma_1(\tau)}\, d\tau + \frac{p\, \beta_2}{\Gamma_1(T)\, \gamma_2}, \qquad p_{\mathrm{sym}} = \frac{p}{\Gamma_1(T)},$$

so $\pi = 1 - e^{-R_0 \pi}$ and $\pi_{\mathrm{sym}} = p\, \pi / \Gamma_1(T)$.

**Heterogeneous population.** With finitely many classes in which a type-$x_i$ susceptible always becomes a type-$y_i$ case, and $p_{\mathrm{sym}}(y_i)$ the probability that a type-$y_i$ case becomes symptomatic, $\pi_{\mathrm{sym}} = \sum_i \pi(y_i)\, p_{\mathrm{sym}}(y_i)$, where $(\pi(y_i))_i$ solves the multitype final-size fixed-point equation. For the multigroup model in which asymptomatic type-$i$ cases become symptomatic at rate $p_i$ and recover at rate $\gamma_i$, $p_{\mathrm{sym}}(y_i) = p_i/(p_i + \gamma_i)$.

**Symptom-defined reproduction numbers do not give a final-size relation.** If $\tilde R_0$ denotes the expected number of symptomatic cases produced by one symptomatic case in a fully susceptible population, then in general $\pi_{\mathrm{sym}} \ne 1 - e^{-\tilde R_0 \pi_{\mathrm{sym}}}$: a test individual can become immune through an asymptomatic infection, so the chance that a given symptomatic case causes the test individual's symptoms depends on how many other symptomatic cases occur.

## Depends on

- [Multitype final-size equation and convergence of its fixed-point iteration](multitype-final-size-fixed-point-iteration.md)
- [Final-size equation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

The final infected fraction equals the probability that a randomly chosen initial susceptible (a test individual) is ever infected. If $K(N)$ cases occur and each infects the test individual independently with probability $R_0/N$, the Poisson limit gives $P(\text{not infected}) \to e^{-R_0 \pi}$, hence $\pi = 1 - e^{-R_0\pi}$. Multiplying by the probability that an infected individual becomes symptomatic gives $\pi_{\mathrm{sym}}$. For the age-of-infection model, $R_0$ is obtained by applying the infection functional to the Green function of the transition operator with a unit impulse at age $0$, giving the asymptomatic contribution plus $p_{\mathrm{sym}}$ times the symptomatic contribution $\beta_2/\gamma_2$. The independence that drives the test-individual argument fails if "infection" is redefined as symptom onset, which is why the formula cannot be applied with $\tilde R_0$.

## Sources

- Barril C, Bliman P-A, Cuadrado S. Final size for epidemic models with asymptomatic transmission. *Bulletin of Mathematical Biology* 85(6):52 (2023), equations (5)–(6), (21)–(22), Section 3 (age-of-infection model and Remark), Section 4 (finite classes). <https://doi.org/10.1007/s11538-023-01159-y> (PMCID: PMC10167127)
