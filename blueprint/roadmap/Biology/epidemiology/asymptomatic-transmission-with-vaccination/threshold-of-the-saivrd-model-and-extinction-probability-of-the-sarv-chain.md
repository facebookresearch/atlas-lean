# Threshold of the SAIVRD model and extinction probability of the SARV chain

**Deterministic SAIVRD model.** Susceptible $S$, asymptomatic infectious $A$, symptomatic (isolated) infected $I$, vaccinated $V$, recovered $R$ and dead $D$ satisfy
$$\begin{aligned}
S' &= B - vS - \tfrac{\beta}{N_0}AS - \mu S, & A' &= \tfrac{\beta}{N_0}AS - (w + \mu)A, & I' &= wA - (\rho + \gamma + \mu)I,\\
V' &= vS - \mu V, & R' &= \gamma I - \mu R, & D' &= \rho I,
\end{aligned}$$
with recruitment $B$, vaccination rate $v$, transmission $\beta$ (only asymptomatic cases transmit), reference population $N_0$, death rate $\mu$, symptom onset $w$, disease death $\rho$ and recovery $\gamma$.

**Theorem.**
1. The set $\{0 \le S + A + I + V + R + D \le B/\mu + N_0\}$ is positively invariant, and $S, A$ stay positive.
2. With

$$R_0 = \frac{B\beta}{N_0(v + \mu)(w + \mu)},$$

the disease-free equilibrium $\big(S, A, I, V, R\big) = \big(\tfrac{B}{v+\mu}, 0, 0, \tfrac{v}{\mu}\tfrac{B}{v+\mu}, 0\big)$ is locally asymptotically stable if and only if $R_0 < 1$.
3. If $R_0 > 1$ there is a unique, locally asymptotically stable endemic equilibrium.

**Stochastic SARV chain.** In the embedded jump chain of a Markov SARV epidemic in a population of size $N$, each asymptomatic case infects at rate $\lambda$ (incidence $\lambda AS/N$), leaves $A$ after an $\mathrm{Exp}(\alpha)$ time, and a fraction $\theta$ of jumps are vaccinations; $R_0^{\mathrm{SARV}} = \lambda(1 - \theta)/\alpha$. As $N \to \infty$, the number of infections caused by one case has generating function $\mathbb{E}u^X = \frac{\alpha}{\alpha + \lambda(1-\theta)(1-u)}$ (geometric), so the probability that an outbreak started by one case goes extinct is

$$q = \min\Big\{1, \frac{1}{R_0^{\mathrm{SARV}}}\Big\}.$$

## Depends on

- [Basic reproduction number as a spectral radius](../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Only $A$ generates new infections, so the next-generation operator is scalar: new infections $\beta S_0 A/N_0$ at the disease-free level $S_0 = B/(v+\mu)$ divided by the exit rate $w + \mu$, which is $R_0$. The endemic state follows from $A' = 0$, giving $S^* = N_0(w+\mu)/\beta$, and then $A^* = \frac{(v+\mu)N_0}{\beta}(R_0 - 1)$, positive exactly when $R_0 > 1$. For the stochastic chain, early on susceptibles are abundant, so infections by one case are Poisson with an exponentially distributed mean, a geometric law with mean $R_0^{\mathrm{SARV}}$; the extinction probability of the approximating Galton–Watson process is the smallest root of $u = \mathbb{E}u^X$, namely $1/R_0^{\mathrm{SARV}}$ when $R_0^{\mathrm{SARV}} > 1$. In the paper both models are run with time-varying fitted parameters for short-term forecasts.

## Sources

- B.-S. Chen, Z.-Y. Wu, Y.-J. Chen and J.-L. Chern, "Data Forecasts of the Epidemic COVID-19 by Deterministic and Stochastic Time-Dependent Models", arXiv:2209.02880 (2022), model and Theorems 2.1–2.3 (Section 2), SARV model and the extinction probability in a large population (Section 4), <https://doi.org/10.48550/arXiv.2209.02880>.
