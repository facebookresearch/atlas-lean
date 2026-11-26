# Negative binomial clone sizes under consecutive seeding

**Model.** A primary tumour contains $N$ clones of constant size. Cells of clone $i$ arrive at a metastatic site as a Poisson process of rate $\lambda_i$, starting at time $0$ with an empty site. Each arriving cell founds an independent linear birth–death process with division rate $b$ and death rate $d$, $b > d > 0$, the same for all clones (neutral diversity). Write

$$k_i = \frac{\lambda_i}{b}, \qquad \rho = 1 - \frac{d}{b}, \qquad r = b - d, \qquad k = \sum_{i=1}^{N} k_i,$$

the seeding influx of clone $i$ per cell generation, the probability that a seeded lineage survives, the net growth rate, and the total influx.

**Mean.** The expected number $\bar y_i(t)$ of clone-$i$ cells solves $\bar y_i' = r\bar y_i + \lambda_i$, $\bar y_i(0) = 0$, so

$$\bar y_i(t) = \frac{k_i}{\rho}\bigl(e^{rt}-1\bigr).$$

**Distribution.** The clone size $y_i(t)$ is negative binomial,

$$\Pr\bigl(y_i(t) = m\bigr) = \frac{\Gamma(m+k_i)}{\Gamma(k_i)\, m!}\, q(t)^{k_i}\bigl(1-q(t)\bigr)^{m}, \qquad q(t) = \frac{k_i}{\bar y_i(t) + k_i} = \frac{\rho}{\rho + e^{rt} - 1},$$

for $m = 0, 1, 2, \dots$; the success probability $q(t)$ is the same for every clone. The clone sizes $y_1(t), \dots, y_N(t)$ are independent.

**Readings.** $y_i(t)$ is the number of successes before $k_i$ failures, a failure being a cell that arrived by seeding rather than by division in the metastasis; equivalently it is the total size of the surviving lineages founded by clone $i$. The influx $k_i$ (seeding relative to division) is the only clone-specific parameter.

## Depends on

- [Negative binomial mass function with real shape](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-pmf.md)

## Proof sketch

This is the classical birth–death–immigration process. Its probability generating function $G(z,t) = \mathbb{E}\, z^{y_i(t)}$ satisfies a linear first-order partial differential equation whose solution is $G = \bigl(q/(1-(1-q)z)\bigr)^{k_i}$ with $q$ as above, the generating function of a negative binomial law with shape $k_i = \lambda_i/b$. The mean $k_i(1-q)/q$ equals $\bar y_i(t)$. Independence across clones holds because the immigration streams are independent Poisson processes and every lineage evolves independently.

## Sources

- A. Heyde, J. G. Reiter, K. Naxerova and M. A. Nowak, "Consecutive seeding and transfer of genetic diversity in metastasis", Proceedings of the National Academy of Sciences of the USA (2019), Model Formulation and Results, Eqs. [1] and [2], and SI Appendix, <https://doi.org/10.1073/pnas.1819408116>, PMCID PMC6628640.
- D. G. Kendall, "On the generalized birth-and-death process", Annals of Mathematical Statistics (1948) (birth–death–immigration process; background).
