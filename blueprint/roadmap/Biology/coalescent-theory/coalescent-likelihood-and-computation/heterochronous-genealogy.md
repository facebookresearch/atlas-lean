# Coalescent likelihood of a serially sampled genealogy

For heterochronous samples, taken at times $0 = s_m < s_{m-1} < \dots < s_1$ with $n_i$ lineages sampled at $s_i$ and $\sum_i n_i = n$, Karcher et al. (2016, section on the coalescent likelihood) write the coalescent likelihood of a fixed genealogy with coalescent times $0 = t_n < t_{n-1} < \dots < t_1$ as follows. The number of active lineages at time $t$ is the number sampled between the present and $t$ minus the number of coalescences in that period; the interval $(0, t_1)$ is partitioned into intervals $I_{0,k}$ that end with the $k$th coalescence and intervals $I_{i,k}$, $i = 1, \dots, m_k$, that end with a sampling event between the $(k-1)$th and $k$th coalescences; and with $C_{i,k} = \binom{n_{i,k}}{2}$ for $n_{i,k}$ active lineages in $I_{i,k}$, given the sampling times,

$$\Pr[g \mid N_e(t), s] \propto \prod_{k=2}^{n} \frac{C_{0,k}}{N_e(t_{k-1})} \exp\Bigl(-\sum_{i=0}^{m_k} \int_{I_{i,k}} \frac{C_{i,k}}{N_e(t)}\, dt\Bigr).$$

The sampling times enter only as fixed times at which lineages are added. Drummond, Nicholls, Rodrigo and Solomon (2002, abstract) use the Kingman coalescent for such temporally spaced sequences to estimate the mutation rate, the population size and the genealogy jointly by Markov chain Monte Carlo.

## Depends on

- [Log-likelihood of one coalescent interval in the skyline model](../../../Biology/coalescent-theory/skyline-plot-estimates-of-population-size/skyline-log-lik.md)

## Expansion

1. The backward process with insertion of the $n_i$ new lineages at each sampling time $s_i$, and its Markov property between events.
2. The interval decomposition by coalescent and sampling events, and the count of active lineages on each interval.
3. The density of the coalescent times and the labelled topology given the sampling times, with the combinatorial factor omitted by the proportionality.
4. The isochronous case $m = 1$ and its agreement with the variable-size Kingman density.

## Sources

- M. D. Karcher, J. A. Palacios, T. Bedford, M. A. Suchard and V. N. Minin, Quantifying and mitigating the effect of preferential sampling on phylodynamic inference, PLoS Comput. Biol. 12 (2016), e1004789, Methods (coalescent likelihood for a heterochronous genealogy) and Fig. 1. <https://doi.org/10.1371/journal.pcbi.1004789>
- A. J. Drummond, G. K. Nicholls, A. G. Rodrigo and W. Solomon, Estimating mutation parameters, population history and genealogy simultaneously from temporally spaced sequence data, Genetics 161 (2002), 1307–1320, abstract. <https://doi.org/10.1093/genetics/161.3.1307>
