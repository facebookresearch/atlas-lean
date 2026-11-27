# fineSTRUCTURE likelihood of a coancestry matrix

Let $n$ individuals be "painted" by a haplotype-copying model, each individual's genome being reconstructed as a mosaic of chunks copied from the other $n-1$ individuals. The coancestry matrix $x = (x_{ij})$ records, for $i \ne j$, the expected number of chunks that recipient $i$ copies from donor $j$; $x_{ii} = 0$.

Let the individuals be partitioned into populations $1, \dots, K$, with $a(i)$ the population of $i$ and $n_b \ge 1$ the size of population $b$. A donor matrix $\theta = (\theta_{ab})$ has $\theta_{ab} \ge 0$ and $\sum_{b=1}^K \theta_{ab} = 1$ for every $a$, with $\theta_{aa} = 0$ whenever $n_a = 1$. Write $\delta_{ab} = 1$ if $a = b$ and $0$ otherwise.

**Model.** A chunk of recipient $i$ is copied from a given donor $j \ne i$ with probability

$$p_{ij} = \frac{\theta_{a(i)a(j)}}{n_{a(j)} - \delta_{a(i)a(j)}},$$

so all members of a population have the same donor and recipient distributions, and $\sum_{j \ne i} p_{ij} = \sum_b \theta_{a(i)b} = 1$. Treating chunks as independent, replacing observed chunk counts by the coancestry entries, and dividing counts by a normalization constant $c > 0$ (an inverse "effective number of independent chunks"), the likelihood is

$$L(x \mid \theta, a) = \prod_{i=1}^{n}\prod_{j \ne i} p_{ij}^{\,x_{ij}/c} = \prod_{a=1}^{K}\prod_{b=1}^{K}\left(\frac{\theta_{ab}}{n_b - \delta_{ab}}\right)^{X_{ab}/c},$$

where $X_{ab} = \sum_{i: a(i) = a}\ \sum_{j \ne i:\, a(j) = b} x_{ij}$ is the total coancestry from population $b$ into population $a$. Hence, for a fixed partition, the data enter the likelihood only through the population-level totals $X_{ab}$.

## Depends on

- [The Li–Stephens copying model](../li-stephens-haplotype-copying-model/hmm.md)

## Expansion

The second form follows by grouping the factors by the populations of recipient and donor: every pair $(i, j)$ with $a(i) = a$, $a(j) = b$ contributes the same base $\theta_{ab}/(n_b - \delta_{ab})$. The constant $c$ corrects both for dependence between chunks (shared tracts counted twice, linkage between adjacent chunks, phasing errors), which inflates variability, and for averaging over painting uncertainty, which deflates it; it is estimated by matching the variance of coancestry contributions across large, approximately independent genomic regions to the variance of the rescaled multinomial model. For unlinked markers the paper shows that a suitable choice of $c$ makes this likelihood asymptotically equivalent to the STRUCTURE likelihood under moderate structure.

## Sources

- D. J. Lawson, G. Hellenthal, S. Myers and D. Falush, "Inference of population structure using dense haplotype data", PLoS Genetics 8 (2012), e1002453, Results, Equation (1) and section "Estimation of the normalization parameter", <https://doi.org/10.1371/journal.pgen.1002453> (PMC3266881).
