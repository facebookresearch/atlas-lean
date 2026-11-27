# Autoregressive model of pool allele frequencies along a chromosome

A pool of $N$ haploid segregants from a cross between two parental strains is sequenced. Divide a chromosome into blocks $i = 1, \dots, L$ small enough that the probability $r \in (0, \tfrac12)$ of an odd number of crossovers between adjacent blocks in one individual is effectively the probability of one crossover, assume no crossover interference, and let $x_i$ be the fraction of the pool carrying the first parent's allele in block $i$. Away from any locus affecting the selected phenotype, each individual carries either parental allele with probability $\tfrac12$.

1. **Discrete chain.** $N x_{i+1} = N x_i - k + j$ with independent $k \sim \mathrm{Bin}(N x_i, r)$ and $j \sim \mathrm{Bin}(N(1 - x_i), r)$. The law $N x_i \sim \mathrm{Bin}(N, \tfrac12)$ is stationary, and the chain is reversible.
2. **Gaussian approximation.** Approximating both binomials by normals,

$$x_{i+1} = (1 - 2r)\,x_i + r + w_i, \qquad w_i \sim \mathcal N\!\Big(0, \frac{r(1-r)}{N}\Big),$$

a first-order autoregressive process whose stationary law is $\mathcal N\big(\tfrac12, \tfrac1{4N}\big)$, matching the mean and variance of $\mathrm{Bin}(N,\tfrac12)/N$.
3. **Observations.** With $d_i$ informative reads in block $i$ and observed allele fraction $y_i$, $d_i y_i \sim \mathrm{Bin}(d_i, x_i)$, approximated by $y_i = x_i + v_i$, $v_i \sim \mathcal N(0, x_i(1-x_i)/d_i)$ with variance at most $1/(4 d_i)$.
4. **Kalman filter.** For the linear-Gaussian model with observation variance $1/(4 d_i)$, the filtered laws $x_i \mid y_1, \dots, y_i \sim \mathcal N(\mu_i, \sigma_i^2)$ satisfy $\mu_0 = \tfrac12$, $\sigma_0^2 = \tfrac1{4N}$ and

$$P_{i-1} = (1-2r)^2 \sigma_{i-1}^2 + \frac{r(1-r)}{N}, \quad K_i = \frac{P_{i-1}}{P_{i-1} + 1/(4d_i)}, \quad \mu_i = (1-2r)\mu_{i-1} + r + K_i\big(y_i - (1-2r)\mu_{i-1} - r\big), \quad \sigma_i^2 = (1 - K_i) P_{i-1},$$

and the Rauch–Tung–Striebel backward recursion gives the smoothed laws $x_i \mid y_1, \dots, y_L$. Blocks without reads ($d_i = 0$) have $K_i = 0$.

## Depends on

- [Binomial probability mass function](../../../../cancer-genomics/detection-power-for-somatic-mutations/binom-pmf.md): the switch counts, the stationary law and the read counts
- [Stationary distribution](../../../../../Probability/markov-chains/kolmogorov-s-criterion-for-reversibility/is-stationary.md)
- [Reversible stochastic matrix](../../../../../Probability/markov-chains/kolmogorov-s-criterion-for-reversibility/is-reversible.md)
- [Kalman filter step](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/step.md): the filtering recursion of item 4

## Proof depends on

- [Detailed balance implies stationarity](../../../../../Probability/markov-chains/kolmogorov-s-criterion-for-reversibility/detailed-balance-is-stationary.md): stationarity of $\mathrm{Bin}(N, \tfrac12)$
- [Autocovariance of the causal AR(1) process](../../../../../Probability/markov-chains/autoregressive-processes/autocovariance-of-a-causal-ar1-process.md): the stationary variance $1/(4N)$
- [The Kalman filter gives the conditional law given the whole observation history](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/kalman-filter-is-the-full-history-posterior.md): the filtered laws

## Expansion

Each of the $N x_i$ carriers of the first allele switches parental origin across the boundary with probability $r$, and likewise for the others, which gives the discrete transition. If the individuals' origins in block $i$ are independent fair coins, each still is after an independent flip with probability $r$, so $\mathrm{Bin}(N,\tfrac12)$ is stationary; each individual's origin is a reversible two-state chain, and so is the count. In the Gaussian version the stationary variance $V$ solves $V = (1-2r)^2 V + r(1-r)/N$, so $V = r(1-r)/(N(1 - (1-2r)^2)) = 1/(4N)$. The continuous model removes the $O(N^2 L)$ cost of forward–backward recursions over $N + 1$ discrete states, so inference time no longer depends on the pool size; Edwards and Gifford (MULTIPOOL) use the discrete chain for small pools and the Kalman version for large ones.

## Sources

- M. D. Edwards, D. K. Gifford, "High-resolution genetic mapping with pooled sequencing", BMC Bioinformatics 13 (Suppl. 6) (2012), S8, <https://doi.org/10.1186/1471-2105-13-s6-s8> (PMC3358661), Methods, "Model specification", "Emission probabilities", "Transition probabilities" and "Inference: continuous model".
