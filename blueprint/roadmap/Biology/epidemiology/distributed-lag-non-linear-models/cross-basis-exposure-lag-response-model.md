# Cross-basis exposure–lag–response model for disease incidence

**Count model.** Let $y_t$ be the number of cases in month $t = 1, \dots, T$ and $P_t$ the population (per 100,000). Cases follow a negative binomial distribution with mean $\mu_t$ and overdispersion parameter $\kappa$, with a log link and a population offset,

$$y_t \mid \mu_t \sim \mathrm{NegBin}(\mu_t = P_t \rho_t, \kappa), \qquad \log \mu_t = \log P_t + \log \rho_t ,$$

so $\rho_t$ is the incidence rate per 100,000. The log rate is a sum of an intercept, random effects for seasonality (a first-order random walk over calendar month) and for interannual variation (exchangeable effects per season), and covariate terms.

**Exposure–lag–response function.** For an exposure series $x_t$ (precipitation, temperature, a drought index) and a maximum lag $L$, the delayed non-linear effect at time $t$ is

$$s(x_{t}, \dots, x_{t-L}) = \sum_{l=0}^{L} f \cdot w(x_{t-l}, l),$$

where the bivariate function $f \cdot w(x, l)$ gives the contribution of exposure level $x$ experienced $l$ time units earlier. Choosing a basis $b_1, \dots, b_J$ for the exposure dimension and a basis $c_1, \dots, c_K$ for the lag dimension (for example natural cubic splines in both) and setting $f \cdot w(x, l) = \sum_{j,k} \theta_{jk}\, b_j(x)\, c_k(l)$ gives

$$s_t = \sum_{j=1}^{J} \sum_{k=1}^{K} \theta_{jk}\, W_{t,jk}, \qquad W_{t,jk} = \sum_{l=0}^{L} b_j(x_{t-l})\, c_k(l) .$$

The $JK$ derived variables $W_{t,jk}$ form the **cross-basis**; they enter $\log \rho_t$ linearly, so the model remains a generalized linear (mixed) model in the coefficients $\theta_{jk}$.

Derived quantities:

- the lag-specific effect of a fixed exposure level $x$ relative to a reference $x_0$ is $f \cdot w(x, l) - f \cdot w(x_0, l)$, a relative risk $\exp(\cdot)$ on the incidence scale;
- the overall cumulative effect over all lags is $\sum_{l=0}^{L} [f \cdot w(x, l) - f \cdot w(x_0, l)]$;
- with $J = 1$ and $b_1(x) = x$ the model reduces to a linear distributed lag model, and with $K = L + 1$ indicator functions of lags it places no smoothness constraint on the lag structure.

## Expansion

Substituting the tensor-product expansion of $f \cdot w$ into the lag sum and exchanging the finite sums produces the cross-basis variables, which is why standard regression machinery (here, Bayesian estimation with integrated nested Laplace approximations) applies unchanged. In the Barbados dengue study, monthly laboratory-confirmed cases over 17 seasons were modelled this way with lags up to 5 months, comparing climate indicators by cross-validated log score and deviance information criterion; drought conditions increased dengue relative risk at lead times of up to 5 months, excess rainfall increased it at lead times of 1–2 months, and bidimensional exposure–lag–response terms described the associations better than linear effects at individual lags.

## Sources

- R. Lowe, A. Gasparrini, C. J. Van Meerbeeck, et al., "Nonlinear and delayed impacts of climate on dengue risk in Barbados: A modelling study", PLoS Medicine 15 (2018), e1002613, Methods ("Model framework", "Exposure–lag–response model"), Eq. (1), <https://doi.org/10.1371/journal.pmed.1002613> (PMC6049902).
