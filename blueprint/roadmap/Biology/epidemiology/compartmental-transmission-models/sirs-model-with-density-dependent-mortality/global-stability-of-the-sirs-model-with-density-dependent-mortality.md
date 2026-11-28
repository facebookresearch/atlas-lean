# Global stability of the SIRS model with density-dependent mortality

**Model.** Susceptible, infective and removed numbers $X, Y, Z$, with $N = X + Y + Z$, birth rate $b$, a fraction $p \in [0,1)$ of infected newborns (vertical transmission), density-dependent death rate $\mu(N)$, strictly increasing in $N$ with $b > \mu(0)$, transmission rate $\beta$, recovery rate $\nu$, loss-of-immunity rate $\alpha$ and disease-induced death rate $\delta$:

$$X' = b(N - pY) - \mu(N) X - \beta X\frac{Y}{N} + \alpha Z, \qquad Y' = bpY + \beta X\frac{Y}{N} - (\mu(N) + \nu + \delta)Y, \qquad Z' = \nu Y - (\alpha + \mu(N))Z,$$

so $N' = (b - \mu(N))N - \delta Y$. The fractions $S = X/N$, $I = Y/N$, $R = Z/N$ satisfy an autonomous system on the simplex $\mathcal{D}^{\mathrm{fra}} = \{S, I, R \ge 0,\ S + I + R = 1\}$ that does not involve $\mu$, and with $S = 1 - I - R$ it reduces to

$$I' = \big(\beta(1 - I - R) - \gamma + \delta I\big) I, \qquad R' = \nu I - \delta(\rho - I) R, \qquad \gamma = (1 - p)b + \nu + \delta, \quad \rho = \frac{b + \alpha}{\delta}.$$

Let $R_0 = \beta/\gamma$.

**Theorem.**

1. *(Disease-free state.)* The disease-free equilibrium $E_0 = (1, 0, 0)$ is globally asymptotically stable in $\mathcal{D}^{\mathrm{fra}}$ if and only if $R_0 \le 1$, and unstable for $R_0 > 1$.
2. *(Endemic state.)* If $R_0 > 1$ there is a unique endemic equilibrium $(I_e, R_e)$, and it is globally asymptotically stable on the reduced invariant set if $\rho \ge 1$, or if $\rho < 1$ and

$$\beta \le \gamma + \frac{\rho(\gamma - \delta)}{1 - \rho}.$$

3. *(Population fate.)* When the endemic state is globally stable, the total population asymptotically follows $N' = (b - \delta I_e - \mu(N))N$, so the disease drives the host to extinction if $b \le \delta I_e + \mu(0)$.

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

For $R_0 \le 1$ the infective fraction itself is a Lyapunov function, since $I' \le (\beta - \gamma)I$ on the simplex. For the endemic state use the equilibrium relations to rewrite the reduced system in deviations and take

$$L = I - I_e - I_e\ln I + \frac{\beta}{2(\nu + \delta R_e)}(R - R_e)^2,$$

whose derivative is $-(\beta - \delta)(I - I_e)^2 - \frac{\beta\delta(\rho - I)}{\nu + \delta R_e}(R - R_e)^2$; the cross terms cancel by the choice of weight. Since $R_0 > 1$ forces $\beta > \delta$, $L' \le 0$ wherever $I \le \rho$, which covers the whole simplex if $\rho \ge 1$. If $\rho < 1$, the $I$-nullcline meets $R = 0$ at $I_u = (\beta - \gamma)/(\beta - \delta)$, and $I_u \le \rho$ is exactly the stated parameter condition; it makes $\{I < \rho\}$ positively invariant and absorbing, so LaSalle's principle applies there.

## Sources

- Alberto d’Onofrio, Piero Manfredi, Ernesto Salinelli, "Lyapunov stability of an SIRS epidemic model with varying population: ecological vs physical approaches", Far East Journal of Mathematical Sciences (FJMS) 117 (2019), 147–160, <https://doi.org/10.17654/ms117020147>. Published version of arXiv:1812.10676, cited next; locators there refer to the arXiv version.
- Alberto d'Onofrio, Piero Manfredi, Ernesto Salinelli, "Lyapunov stability of an SIRS epidemic model with varying population", arXiv (2018). Section 2 (model and fraction system), Theorems 1 and 2, Remarks 3 and 4. <https://doi.org/10.48550/arXiv.1812.10676>
