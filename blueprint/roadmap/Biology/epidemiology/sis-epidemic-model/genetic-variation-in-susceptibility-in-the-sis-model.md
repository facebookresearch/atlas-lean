# Genetic variation in susceptibility in the SIS model and liability-scale heritability

**Homogeneous SIS model.** In a herd of $N$ individuals with $S$ susceptible and $I = N - S$ infected, infections occur at rate $\beta S I/N$ and recoveries at rate $\alpha I$ (mean infectious period $1/\alpha$). The equilibrium prevalence solves $\beta S I/N = \alpha I$:

$$P_{\mathrm{eq}} = \frac IN = 1 - \frac\alpha\beta = 1 - \frac1{R_0}, \qquad R_0 = \beta/\alpha,$$

for $R_0 > 1$ (and $P_{\mathrm{eq}} = 0$ for $R_0 \le 1$).

**Individual susceptibility.** Give susceptible individual $i$ the transmission parameter $\beta_i = \beta\gamma_i$ with relative susceptibility

$$\gamma_i = e^{A_{\gamma i} + E_{\gamma i}}, \qquad A_\gamma \sim N(0,\sigma^2_{A\gamma}), \quad E_\gamma \sim N(0,\sigma^2_{E\gamma}),$$

where $A_{\gamma i}$ is the breeding value and $E_{\gamma i}$ a permanent environmental effect for log-susceptibility, so that individual $i$ becomes infected at rate $\beta\gamma_iI/N$ and, over a time step of length $1$, with probability $1 - e^{-\beta\gamma_iI/N}$. Offspring breeding values follow the infinitesimal model $A_{\gamma i} = \tfrac12A_{\gamma,\mathrm{sire}} + \tfrac12A_{\gamma,\mathrm{dam}} + MS_{\gamma i}$, $MS_{\gamma i} \sim N(0,\tfrac12\sigma^2_{A\gamma})$.

**Liability-scale heritability.** Because infection is a Poisson event with log-linear rate, $P(\text{infected}) = 1 - \exp(-e^{\eta})$ with $\eta = \log(\beta I/N) + A_{\gamma} + E_\gamma$: a generalized linear mixed model with complementary log-log link. Its equivalent threshold model has a standard Gumbel liability residual with variance $\pi^2/6$, so the heritability of log-susceptibility on the liability scale is

$$h^2_{\gamma,\mathrm{liab}} = \frac{\sigma^2_{A\gamma}}{\sigma^2_{A\gamma} + \sigma^2_{E\gamma} + \pi^2/6}.$$

With heterogeneous susceptibility the formula $1 - 1/R_0$ is no longer exact for the mean prevalence.

## Depends on

- [Endemic equilibrium of the SIS model](is-solution-const-endemic.md)
- [Basic reproduction number of the SIS model](r0-eq.md)

## Expansion

The complementary log-log link is the inverse of $\eta \mapsto 1 - \exp(-e^\eta)$, which is the CDF $F(x) = 1 - \exp(-e^x)$ of the minimum-type Gumbel law; hence $1 - \exp(-e^\eta) = P(\epsilon \le \eta)$ for $\epsilon \sim F$, a threshold model whose residual variance is the Gumbel variance $\pi^2/6$. Additive genetic and permanent environmental variances on the log-rate scale then enter the liability decomposition directly.

## Sources

- Andries D. Hulst, M.C.M. de Jong and Piter Bijma, "Why genetic selection to reduce the prevalence of infectious diseases is way more promising than currently believed", Genetics (2021), <https://doi.org/10.1093/genetics/iyab024> (PMC8049556). Methods, Eqs. (1)–(11).
