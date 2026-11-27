# Average squared distance clock under the generalized stepwise mutation model

For microsatellite allele lengths $x_1, \dots, x_n$ ($n \ge 2$), the average squared distance is

$$\mathrm{ASD} = \frac{1}{n(n-1)} \sum_{i \ne j} (x_i - x_j)^2 .$$

Under the generalized stepwise mutation model, mutations occur along each lineage as a Poisson process of rate $\mu$ per generation, each mutation adds an independent integer step $\xi$ with $\mathbb{E}[\xi] = 0$ and $\mathbb{E}[\xi^2] = \sigma_\xi^2 < \infty$ to the repeat length, and lengths are unconstrained. If two alleles descend from a common ancestor $T$ generations ago, then

$$\mathbb{E}\big[(x_1 - x_2)^2 \mid T\big] = 2 \mu \sigma_\xi^2\, T .$$

Consequently, for a sample whose pairwise times to the most recent common ancestor are $T_{ij}$, $\mathbb{E}[\mathrm{ASD} \mid (T_{ij})] = 2\mu\sigma_\xi^2\, \bar T$, where $\bar T$ is the average of $T_{ij}$ over ordered pairs $i \ne j$. For the single-step model ($\xi = \pm 1$ with probability $\tfrac12$ each) $\sigma_\xi^2 = 1$.

## Depends on

- [Identity in state under the stepwise mutation model](../../../../population-genetics/infinite-alleles-model-and-homozygosity/stepwise-mutation-model-homozygosity.md)

## Expansion

The two alleles differ by the sum of the steps accumulated on the two lineages since their ancestor. The number of mutations on total branch length $2T$ is Poisson with mean $2\mu T$, and given that number the steps are i.i.d. with mean zero, so $x_1 - x_2$ is a compound Poisson variable with mean $0$ and variance $2\mu T\, \mathbb{E}[\xi^2]$ (Wald's identity). Averaging over pairs gives the sample statement. The clock rate depends on the step distribution as well as on $\mu$: direct observation of 2,058 germline mutations in Icelandic pedigrees found that $32\%$ of mutations at di-nucleotide microsatellites are multi-step versus $1\%$ at tetra-nucleotides, which raises $\sigma_\xi^2$ above $1$ for di-nucleotide loci. Sun et al. combine ASD with heterozygosity of the flanking sequence and human-macaque divergence in a hierarchical model, so that the directly measured microsatellite mutation rate calibrates the sequence mutation rate and divergence times without fossil calibration.

## Sources

- J. X. Sun, A. Helgason, G. Masson et al., "A direct characterization of human mutation based on microsatellites", Nature Genetics 44 (2012), <https://doi.org/10.1038/ng.2398> (PMC3459271). Online Methods (definition of ASD and the model of microsatellite evolution).
