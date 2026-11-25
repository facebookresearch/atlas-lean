# The Poisson random field as the stationary limit of immigrating Wright–Fisher diffusions

This page covers a research programme around the model of Sawyer and Hartl. New mutations arrive as a Poisson process, and each then follows an independent Wright–Fisher diffusion started at a small frequency $p_M$. The programme is to show that at stationarity the configuration of frequencies is a Poisson point process whose intensity converges, as $M \to \infty$ and vaguely on compact subsets of $(0, 1]$, to the density $\phi(x)\, dx$ of [the expected site frequency spectrum under the Poisson random field](expected-sfs.md).

A statement in this programme first fixes the model from the source: the entry frequency ($p_M = 1/M$ or $1/(2N)$), the units of the arrival rate, the infinite-sites assumption, the independence of the sites, and the convention for selection.

## Expansion

Split the programme into separately stated results, each with hypotheses fixed from a source.

Prerequisites:

- [Expected site frequency spectrum under the Poisson random field](expected-sfs.md)
- [Sawyer–Hartl Poisson random field density](prf-density.md)
- [Occupation-time formula and mean absorption time with selection](../sojourn-times-of-the-wright-fisher-diffusion/occupation-time-formula-and-mean-absorption-time.md)
- [Poisson point process with finite intensity](../../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md)
- [Exponential interarrivals give a Poisson process](../../../../Probability/point-processes/poisson-processes/is-poisson-process-count.md)

## Sources

- S. A. Sawyer and D. L. Hartl, Population genetics of polymorphism and divergence, *Genetics* 132 (1992), 1161–1176, <https://pmc.ncbi.nlm.nih.gov/articles/PMC1205236/> (model construction and equilibrium density).
- M. Kimura, The number of heterozygous nucleotide sites maintained in a finite population due to steady flux of mutations, *Genetics* 61 (1969), 893–903, <https://pmc.ncbi.nlm.nih.gov/articles/PMC1212250/> (steady flux of mutations).
