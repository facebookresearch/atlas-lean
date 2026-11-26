# Probability of acquiring resistance in a growing drug-tolerant population

**Model.** A population of $N_0$ drug-tolerant cells evolves as a linear birth–death process with birth rate $b$ and death rate $d$, $b > d \ge 0$, so its expected size is $N_0 e^{(b-d)t}$. At each birth, independently, a daughter acquires a specific resistance mutation with probability $\mu \in (0,1)$.

**Birth count.** The expected number of birth events on $[0, T]$ is

$$B(T) = \int_0^T b\,N_0 e^{(b-d)t}\,dt = \frac{b\,N_0\bigl(e^{(b-d)T} - 1\bigr)}{b-d} \;\approx\; \frac{b\,N_0\,e^{(b-d)T}}{b-d} \quad \text{for } (b-d)T \gg 1.$$

**Acquisition probability.** Treating the birth count as fixed at its mean, the probability that at least one resistance mutation has arisen by time $T$ is

$$R(T) = 1 - (1-\mu)^{B(T)} \;\approx\; \mu\,B(T) \quad \text{when } \mu B(T) \ll 1.$$

This is an upper bound on the probability that a resistant lineage is established, since a new resistant cell's lineage may still go extinct.

## Depends on

- [Mean population size of the linear birth–death process](../../../../Probability/branching-processes/linear-birth-death-process/has-sum-mul-prob.md)

## Expansion

Each birth is an independent Bernoulli($\mu$) trial for the mutation, so the chance of no mutation in $B$ births is $(1-\mu)^B$; replacing the random number of births by its expectation gives the formula, and $1-(1-\mu)^B \approx \mu B$ for small $\mu B$. The rate $\mu$ is the effective rate for the specific resistance allele: for EGFR T790M in a cell line with about ten EGFR copies and a CpG-deamination hotspot it was taken about 360 times the average per-site rate. With $N_0 \approx 150$ tolerant cells and net growth $b - d \approx 0.0015$ per hour, the approximation agreed with Monte Carlo simulations of the branching process and showed that slowly dividing drug-tolerant cells can acquire T790M within months.

## Sources

- A. N. Hata, M. J. Niederst, H. L. Archibald et al., "Tumor cells can follow distinct evolutionary paths to become resistant to epidermal growth factor receptor inhibition", Nature Medicine (2016), Online Methods ("Mathematical modeling of evolution of T790M from drug tolerant cells"), <https://doi.org/10.1038/nm.4040>.
