# Coalescence rate from recurrent selective sweeps

Consider an autosomal neutral site at position $x$ on a lineage of length $T$ generations, during which beneficial substitutions fixed at known positions. Group the substituted positions into annotation classes $i_S$ with position sets $a(i_S)$. A fraction $\alpha(i_S)$ of the substitutions in class $i_S$ were beneficial, with additive selection coefficients drawn from a density $g(s \mid i_S)$. Let $r(x,y)$ be the recombination distance between $x$ and a substitution at $y$ on the same chromosome, and let $\bar N_e$ be the average effective population size. Treating sweeps as rare, independent and complete, the expected per-generation rate at which two lineages at $x$ are forced to coalesce by sweeps is

$$S(x) = \frac{1}{T}\sum_{i_S} \alpha(i_S) \sum_{y\in a(i_S)} \int e^{-r(x,y)\,\tau(s,\bar N_e)}\, g(s\mid i_S)\, ds,$$

where $\tau(s, N_e)$ is the expected fixation time of a beneficial allele, given by the diffusion approximation

$$\tau(s, N_e) = \frac{2\bigl(\ln(4N_e s) + \gamma - (4N_e s)^{-1}\bigr)}{s},$$

with $\gamma$ the Euler–Mascheroni constant.

## Proof sketch

Each beneficial substitution at $y$ is a sweep lasting about $\tau$ generations. A neutral lineage at distance $r$ escapes the sweeping haplotype by recombination with probability about $1 - e^{-r\tau}$. Two sampled lineages that both stay linked trace back to the single founding beneficial haplotype and coalesce, which happens with probability about $e^{-r\tau}$. Spreading the expected number of beneficial substitutions in a class over the $T$ generations of the lineage turns these per-sweep probabilities into a rate. The sum over classes and positions assumes sweeps do not overlap in time. The fixation-time formula is the diffusion expectation for a new semidominant mutation with $4N_es \gg 1$.

## Proof depends on

- [Probability that a neutral lineage stays linked during a deterministic sweep](hitchhiking-deterministic-escape-probability.md)

## Sources

- E. Elyashiv, S. Sattath, T. T. Hu, A. Strutsovsky, G. McVicker, P. Andolfatto, G. Coop, G. Sella, *A genomic map of the effects of linked selection in Drosophila*, PLoS Genetics 12 (2016), e1006130, <https://doi.org/10.1371/journal.pgen.1006130>, PMCID PMC4990265. Sweep model Eq. (3); fixation time Eq. (4).
