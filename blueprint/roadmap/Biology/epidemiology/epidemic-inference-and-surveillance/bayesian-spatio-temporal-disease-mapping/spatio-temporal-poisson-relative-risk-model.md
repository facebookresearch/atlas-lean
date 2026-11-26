# Spatio-temporal Poisson relative-risk model

Let areas $i = 1, \dots, n$ have populations $P_{ij}$ in age groups $j$, and let $f_j$ be the national incidence in age group $j$. The expected count of area $i$ by indirect standardization is

$$E_i = \sum_j f_j P_{ij}. \tag{1}$$

The observed counts $O_{it}$ (area $i$, day $t$) follow

$$O_{it} \sim \mathrm{Poisson}(E_i\, \mu_{it}), \qquad \log \mu_{it} = \alpha + \sum_k \beta_k X_{ik} + p\big(X_{i,t-\ell}\big) + s_i + u_i + \delta_t + \varepsilon_t, \tag{2}$$

where $\log E_i$ is an offset, $X_{ik}$ are area-level covariates, $p$ is a cubic polynomial in a covariate lagged by $\ell$ days, $s_i$ is a spatially structured effect (Besag intrinsic conditional autoregressive model on the contiguity graph: given the others, $s_i$ is normal with mean the average of $s$ over the $n_i$ neighbours of $i$ and variance $\sigma_s^2 / n_i$), $u_i$ and $\varepsilon_t$ are independent Gaussian effects, and $\delta_t$ is a second-order random walk ($\delta_t - 2\delta_{t-1} + \delta_{t-2}$ independent normal with mean zero and common variance).

Properties:

- with all effects zero except $\alpha = 0$, $\mathbb{E}[O_{it}] = E_i$: $\mu_{it}$ is the relative risk with respect to the age-standardized expectation, so differences in age structure between areas do not appear as risk differences;
- $\sum_i \sum_j f_j P_{ij} = \sum_j f_j P_{\cdot j}$ equals the national total of cases when the $f_j$ are the observed national age-specific incidences, so the expected counts are calibrated to the overall count;
- the intrinsic autoregressive and random-walk priors are improper and invariant under adding a constant to all $s_i$ (or a constant or a linear trend in $t$ to $\delta_t$), so a sum-to-zero constraint is needed to identify them separately from $\alpha$.

## Expansion

The structured effects borrow strength between neighbouring areas and adjacent days, and the unstructured effects absorb area- or day-specific noise; together they correspond to the Besag–York–Mollié decomposition for space plus a smooth temporal trend. Fitting uses integrated nested Laplace approximation for this latent Gaussian model. Lagged temperatures with $\ell$ from 2 to 14 days reflect the incubation period between infection and detection, and the cubic polynomial allows non-linear effects. Highly correlated covariates (population density, visitors, companies; the three temperature summaries) were entered one at a time. In the Spanish provinces during the first month of the COVID-19 epidemic, temperature showed no clear association with the relative risk once the structured effects were included.

## Sources

- Á. Briz-Redón, Á. Serrano-Aroca, "A spatio-temporal analysis for exploring the effect of temperature on COVID-19 early evolution in Spain", Science of the Total Environment (2020) 138811, Data (Eq. 1), Methodology, "Statistical modelling approach", Eq. (2), and Results, <https://doi.org/10.1016/j.scitotenv.2020.138811> (PMC7194829).
