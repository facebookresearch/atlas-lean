# Random-effects model of stratified LD-score regression

Let $\mu$ be a measure on a measurable space $\Omega$ and let $N, M$ be natural numbers (individuals and markers). A stratified LD-score model with per-marker second moments consists of real numbers $\sigma^2_1, \dots, \sigma^2_M$ (the effect second moments) and $\sigma^2_e$ (the noise second moment), and real functions $\beta_1, \dots, \beta_M$ (effects) and $\varepsilon_1, \dots, \varepsilon_N$ (noise) on $\Omega$, square integrable with respect to $\mu$, such that for all markers $k, l$ and individuals $i, i'$

- $\int \beta_k \beta_l \, d\mu = \sigma^2_k$ if $k = l$, and $0$ otherwise;
- $\int \varepsilon_i \varepsilon_{i'} \, d\mu = \sigma^2_e$ if $i = i'$, and $0$ otherwise;
- $\int \beta_k \varepsilon_i \, d\mu = 0$.

The measure is arbitrary and no means are imposed, so these parameters are raw second moments; they are variances and covariances when $\mu$ is a probability measure and the effects and noise are centred. All statements are conditional on the genotype matrix.
