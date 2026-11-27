# Reproduction number and forward bifurcation of the staged pneumonia model

**Model.** Let $S, E, I_1, I_2, R \ge 0$ (susceptible, exposed, first-stage infective, second-stage infective, recovered), $N = S + E + I_1 + I_2 + R$, and let all parameters be positive except $u, p \in [0,1]$: recruitment $\Lambda$, natural death $\mu$, transmission rates $\beta_1, \beta_2$ from $I_1, I_2$, latency exit $\alpha$, treatment coverage $u$ of $I_1$ with treatment rate $\delta$ and success probability $p$, untreated progression $\xi$ from $I_1$ to $I_2$, recovery $\gamma$ and extra death $\epsilon$ in $I_2$, waning immunity $\eta$:

$$\begin{aligned}
\dot S &= \Lambda - \frac{S(\beta_1 I_1 + \beta_2 I_2)}{N} + \eta R - \mu S,\\
\dot E &= \frac{S(\beta_1 I_1 + \beta_2 I_2)}{N} - (\mu+\alpha) E,\\
\dot I_1 &= \alpha E - \big(u\delta + (1-u)\xi + \mu\big) I_1,\\
\dot I_2 &= \big((1-p)u\delta + (1-u)\xi\big) I_1 - (\mu+\gamma+\epsilon) I_2,\\
\dot R &= p u \delta I_1 + \gamma I_2 - (\mu+\eta) R.
\end{aligned}$$

The nonnegative orthant is forward invariant, and $N$ satisfies $\dot N = \Lambda - \mu N - \epsilon I_2 \le \Lambda - \mu N$, so solutions enter $\{N \le \Lambda/\mu + \sigma\}$ for every $\sigma > 0$. Write $k_1 = u\delta + (1-u)\xi + \mu$ and $k_2 = \mu+\gamma+\epsilon$.

1. The pneumonia-free equilibrium is $E_0 = (\Lambda/\mu, 0, 0, 0, 0)$, and the next-generation reproduction number is

$$R_0 = R_1 + R_2, \qquad R_1 = \frac{\beta_1 \alpha}{(\alpha+\mu) k_1}, \qquad R_2 = \frac{\beta_2\, \alpha\, \big((1-p)u\delta + (1-u)\xi\big)}{(\alpha+\mu)\, k_1\, k_2},$$

where $R_1$ and $R_2$ are the secondary infections produced while in stage 1 and stage 2.
2. $E_0$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.
3. At $R_0 = 1$ the system undergoes a forward (transcritical) bifurcation: no endemic equilibrium bifurcates into $R_0 < 1$, and for $R_0 > 1$ close to $1$ the endemic equilibrium is positive and locally asymptotically stable. Backward bifurcation does not occur for any parameter values.
4. $R_0$ is nonincreasing in the treatment success probability $p$, strictly decreasing when $\beta_2 u \delta > 0$.

## Expansion

With $F$ the new-infection matrix (nonzero only in the $E$ row) and $V$ the transition matrix on $(E, I_1, I_2)$, $R_0 = \rho(FV^{-1})$ is the expected number of new infections from one exposed individual: it reaches $I_1$ with probability $\alpha/(\alpha+\mu)$, infects at rate $\beta_1$ for mean time $1/k_1$, moves to $I_2$ with probability $((1-p)u\delta + (1-u)\xi)/k_1$, and there infects at rate $\beta_2$ for mean time $1/k_2$. The Jacobian at $E_0$ factors as $(\lambda+\mu)(\lambda+\eta+\mu)$ times the characteristic polynomial of $F - V$, whose spectral abscissa is negative exactly when $R_0 < 1$. For item 3, taking $\beta_2$ as bifurcation parameter, the Castillo-Chavez–Song coefficients satisfy $a < 0$ and $b > 0$ for all admissible parameters. Item 4 follows because $p$ enters only through the factor $(1-p)u\delta$ in $R_2$. The effect of coverage $u$ depends on the parameters: for example, $R_1$ decreases in $u$ exactly when $\delta > \xi$. In the source the model is then fitted to Jakarta incidence with seasonally forced transmission $\beta_i(t) = a_i + b_i\cos(2\pi c t)$ and used for an optimal treatment-coverage control problem.

## Sources

- Dipo Aldila, Nadya Awdinda, Fatmawati, Faishal F. Herdicho, Meksianis Z. Ndii, Chidozie W. Chukwu, "Optimal control of pneumonia transmission model with seasonal factor: Learning from Jakarta incidence data", *Heliyon*, article e18096 (2023), Section 2.1 (Equations (1a)–(1e)), Section 2.2 (Theorems 1 and 2), Sections 3.1–3.5 (Equation (3), Theorems 3 and 4). <https://doi.org/10.1016/j.heliyon.2023.e18096>. PMCID: PMC10375561.
