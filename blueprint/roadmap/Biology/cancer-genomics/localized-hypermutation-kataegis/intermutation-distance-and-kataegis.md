# Intermutation distance and regional hypermutation

Let the somatic substitutions of a genome be listed in genomic order as positions $p_1 < p_2 < \dots < p_n$ within a chromosome. The intermutation distance of the $i$-th substitution is

$$d_i = p_i - p_{i-1}, \qquad i \ge 2,$$

and a rainfall plot displays $\log_{10} d_i$ against $p_i$, coloured by substitution class. Two null models of uniform mutation give closely related gap laws:

- **Discrete (Bernoulli) model.** Each base is mutated independently with probability $q \in (0,1)$. Then, on an unbounded chromosome, the gaps $d_i$ are independent geometric variables, $\Pr(d_i = x) = (1-q)^{x-1} q$ for $x = 1, 2, \dots$, with mean $1/q$ and $\Pr(d_i \le x) = 1 - (1-q)^x$.
- **Continuous (Poisson process) model.** Mutations form a homogeneous Poisson process of rate $\lambda$ per base. Then the gaps are independent exponential variables with mean $1/\lambda$ and $\Pr(d_i \le x) = 1 - e^{-\lambda x}$.

Recording at each base whether a Poisson process of rate $\lambda$ placed at least one mutation there gives the discrete model with $q = 1 - e^{-\lambda}$, not $q = \lambda$; with this $q$ the geometric distribution function equals the exponential one at every integer, $1 - (1-q)^x = 1 - e^{-\lambda x}$, while taking $q = \lambda$ is only a first-order approximation for small $\lambda$. Under either model, runs of many consecutive small $d_i$ are exponentially unlikely. Kataegis is the occurrence of localized clusters in which many consecutive substitutions have intermutation distances orders of magnitude below the genome-wide mean, typically with a consistent class and sequence context within a cluster.

## Remarks

Plotting the gap rather than a binned density is what makes a cluster visible at any scale: a region whose mutations are $10^2$ bases apart in a genome averaging $10^5$ appears as a band three decades below the bulk, regardless of how many mutations it contains. The exponential null is the right baseline because a Poisson process has independent increments; departures therefore implicate a process acting processively along a short stretch of DNA rather than independently at each site. Two features of such clusters carry mechanistic information: the strand-consistent runs of a single substitution class, indicating processive action on one strand, and the restriction of the mutated base to a specific flanking context, which points to an enzymatic deaminase rather than to a background damage-repair imbalance. The same statistic distinguishes genuine clustering from an excess of adjacent double substitutions, which produce $d_i = 1$ and must be counted separately.

## Sources

- Nik-Zainal S, Alexandrov LB, Wedge DC, et al. Mutational processes molding the genomes of 21 breast cancers. *Cell* 149:979-993 (2012), "kataegis" and Figures 3 and S2. DOI <https://doi.org/10.1016/j.cell.2012.04.024>. PMCID PMC3414841.
