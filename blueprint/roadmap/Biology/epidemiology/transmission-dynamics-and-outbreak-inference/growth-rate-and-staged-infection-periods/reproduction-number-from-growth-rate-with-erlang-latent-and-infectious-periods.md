# Reproduction number from growth rate with Erlang latent and infectious periods

Consider a staged susceptible-exposed-infectious-removed model in a fully susceptible population: an infected individual passes through $m \ge 1$ exposed stages, each with exit rate $m\sigma$, so the latent period is Erlang with shape $m$ and mean $1/\sigma$; then through $n \ge 1$ infectious stages, each with exit rate $n\gamma$, so the infectious period is Erlang with shape $n$ and mean $1/\gamma$; and transmits at constant rate $\beta > 0$ while infectious, so that

$$\mathcal{R}_0 = \frac{\beta}{\gamma}.$$

Let $r > 0$ be the exponential growth rate of the linearization at the disease-free equilibrium. Then

$$\mathcal{R}_0 \;=\; \frac{r}{\gamma} \cdot \frac{\bigl(1 + \tfrac{r}{m\sigma}\bigr)^{m}}{1 - \bigl(1 + \tfrac{r}{n\gamma}\bigr)^{-n}} .$$

Special cases:

- $m = n = 1$ (exponential latent and infectious periods): $\mathcal{R}_0 = \bigl(1 + \tfrac{r}{\sigma}\bigr)\bigl(1 + \tfrac{r}{\gamma}\bigr)$.
- $m, n \to \infty$ (fixed latent period $1/\sigma$ and fixed infectious period $1/\gamma$): $\mathcal{R}_0 = \dfrac{r}{\gamma} \cdot \dfrac{e^{r/\sigma}}{1 - e^{-r/\gamma}}$.
- $\sigma \to \infty$ (no latent period, $n = 1$): $\mathcal{R}_0 = 1 + r/\gamma$.

For fixed means $1/\sigma$ and $1/\gamma$ and fixed $r$, the map $m \mapsto (1 + r/(m\sigma))^{m}$ is increasing, so concentrating the latent period around its mean increases the reproduction number implied by the observed growth rate. The doubling time is $t_d = \log 2 / r$.

## Depends on

- [For β ≥ 0 and σ, γ > 0, the SEIR R₀ = ρ(F V⁻¹) equals β / γ](../../seir-epidemic-model/r0-eq.md)

## Proof depends on

- [Reproductive number from growth rate and generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)
- [Moment generating function of the gamma distribution](../../../../Probability/distributions/continuous/gamma-distribution/gamma-mgf/mgf-gamma-measure-of-lt.md)

## Proof sketch

Write the expected infectivity of an individual at age of infection $a$ as $\beta\, \mathbb{P}(\text{infectious at } a)$. In the renewal (Euler-Lotka) form, exponential growth at rate $r$ requires

$$1 \;=\; \beta \int_0^{\infty} e^{-ra}\, \mathbb{P}(\text{infectious at age } a)\, da .$$

Let $T_E \sim \mathrm{Erlang}(m, m\sigma)$ and $T_I \sim \mathrm{Erlang}(n, n\gamma)$ be independent. Then $\mathbb{P}(\text{infectious at } a) = \mathbb{P}(T_E \le a < T_E + T_I)$ and, by Fubini and independence,

$$\int_0^\infty e^{-ra}\,\mathbb{P}(T_E \le a < T_E+T_I)\,da \;=\; \mathbb{E}\bigl[e^{-rT_E}\bigr] \cdot \mathbb{E}\Bigl[\int_0^{T_I} e^{-ru}\,du\Bigr] \;=\; \mathbb{E}\bigl[e^{-rT_E}\bigr]\cdot \frac{1 - \mathbb{E}[e^{-rT_I}]}{r} .$$

The Laplace transform of an Erlang law with shape $k$ and rate $k\lambda$ is $\mathbb{E}[e^{-rT}] = (1 + r/(k\lambda))^{-k}$, so

$$1 \;=\; \frac{\beta}{r}\,\Bigl(1 + \frac{r}{m\sigma}\Bigr)^{-m}\Bigl[1 - \Bigl(1 + \frac{r}{n\gamma}\Bigr)^{-n}\Bigr],$$

and substituting $\beta = \gamma \mathcal{R}_0$ gives the stated formula. The limits follow from $(1 + x/k)^{k} \to e^{x}$, and $m \mapsto (1+x/m)^m$ is increasing in $m$ for $x > 0$, which gives the monotonicity claim: more peaked latent periods delay transmission less variably, so a given growth rate demands more secondary cases per case.

Numerically the shape matters a great deal. With an estimated early growth rate $r$ in the range $0.21$-$0.30$ per day, the doubling time $\log 2 / r$ lies between $2.3$ and $3.3$ days, and with latent and infectious periods consistent with a serial interval of $6$-$9$ days this conversion returns a median basic reproduction number near $5.7$, well above the value near $2.2$ obtained from slower early growth estimates. The consequence for control is immediate, since the fraction of the population that must be immune for elimination is $1 - 1/\mathcal{R}_0$: about $55\%$ at $\mathcal{R}_0 = 2.2$ and about $82\%$ at $\mathcal{R}_0 = 5.7$.

## Sources

- S. Sanche, Y. T. Lin, C. Xu, E. Romero-Severson, N. Hengartner, R. Ke, "High contagiousness and rapid spread of severe acute respiratory syndrome coronavirus 2", Emerging Infectious Diseases 26(7) (2020) 1470-1477, Results ("Estimating R0") and Appendix 2, which performs this conversion following Wearing and Rohani, <https://doi.org/10.3201/eid2607.200282> (PMC7323562).
- H. J. Wearing, P. Rohani, M. J. Keeling, "Appropriate models for the management of infectious diseases", PLoS Medicine 2(7) (2005) e174, for the staged-period conversion between growth rate and reproduction number, <https://doi.org/10.1371/journal.pmed.0020174>.
