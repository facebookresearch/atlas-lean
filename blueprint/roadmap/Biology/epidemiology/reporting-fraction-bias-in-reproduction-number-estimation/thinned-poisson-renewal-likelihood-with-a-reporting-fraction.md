# Thinned Poisson renewal likelihood with a reporting fraction

Consider the initial phase of an outbreak in a homogeneously mixing population with an unlimited supply of susceptibles. Let $N_0$ be the number of initial cases and $N_1,\dots,N_T$ the true numbers of new cases on days $1,\dots,T$ (with $N_s = 0$ for $s<0$). Let the serial interval be a probability vector $p = (p_1,\dots,p_k)$, where $p_j \ge 0$ is the probability that an infectee shows symptoms $j$ days after the infector and $\sum_{j=1}^k p_j = 1$. Assume that, conditionally on the past, $N_t$ is Poisson with mean

$$\mu_t = R_0 \sum_{j=1}^{\min(k,t)} p_j\, N_{t-j}, \qquad t = 1,\dots,T,$$

so the likelihood of $(N_1,\dots,N_T)$ is

$$L(R_0,p) = \prod_{t=1}^{T} \frac{e^{-\mu_t}\mu_t^{N_t}}{N_t!}.$$

**(i) Complete data.** For a known serial interval and $\sum_{t=1}^T \sum_{j=1}^{\min(k,t)} p_j N_{t-j} > 0$, the maximum likelihood estimator of $R_0$ is

$$\hat R_0 = \frac{\sum_{t=1}^{T} N_t}{\sum_{t=1}^{T}\sum_{j=1}^{\min(k,t)} p_j N_{t-j}}.$$

When $p_1 = 1$ (one serial interval per time step, i.e. data grouped by generation) this reduces to the branching-process estimator $\sum_{t=1}^T N_t / \sum_{t=1}^T N_{t-1}$.

**(ii) Incomplete reporting.** Suppose only $M_t = q_t N_t$ cases are observed on day $t$, with known reporting fractions $q_t > 0$. Substituting $N_t = M_t/q_t$ gives the thinned likelihood

$$L(R_0,p,q) = \prod_{t=1}^{T} \frac{e^{-\mu_t}\mu_t^{M_t/q_t}}{(M_t/q_t)!}, \qquad \mu_t = R_0\sum_{j=1}^{\min(k,t)} p_j\,\frac{M_{t-j}}{q_{t-j}},$$

and the corresponding estimator of $R_0$ for known $p$ is

$$\tilde R_0 = \frac{\sum_{t=1}^{T} M_t/q_t}{\sum_{t=1}^{T}\sum_{j=1}^{\min(k,t)} p_j\, M_{t-j}/q_{t-j}}.$$

## Expansion

The log-likelihood in $R_0$ is $\sum_t \left(N_t \log(R_0 c_t) - R_0 c_t\right) + \text{const}$ with $c_t = \sum_j p_j N_{t-j}$; it is strictly concave for $\sum_t N_t > 0$, and setting its derivative $\sum_t N_t/R_0 - \sum_t c_t$ to zero gives (i). Part (ii) is the same computation applied to the reconstructed counts $M_t/q_t$. The serial-interval parameters (multinomial, or a truncated gamma or Weibull) are estimated jointly by maximizing the same likelihood. In practice $q_t$ is rarely known; the companion result shows when ignoring it matters.

## Sources

- Laura F. White, Marcello Pagano, "Reporting errors in infectious disease outbreaks, with an application to Pandemic Influenza A/H1N1", *Epidemiologic Perspectives & Innovations* 7:12 (2010), Methods, Equations (1)–(3) and the section "Estimation of $R_0$". <https://doi.org/10.1186/1742-5573-7-12>. PMCID: PMC3018365.
