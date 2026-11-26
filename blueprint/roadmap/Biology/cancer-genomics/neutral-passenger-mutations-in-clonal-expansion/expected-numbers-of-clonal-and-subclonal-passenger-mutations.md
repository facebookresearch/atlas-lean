# Expected numbers of clonal and subclonal passenger mutations

In the multi-type birth–death model of a clonal expansion started by one cell (birth rate $b$, death rate $d$, $\delta = d/b \in [0,1)$, passenger probability $u$ per division, infinitely many alleles), condition on non-extinction and let the final population be large.

**Subclonal passengers.** The expected number of passengers acquired during the expansion that end at a cell fraction strictly between $\alpha$ and $1$, for $0 < \alpha < 1$, is

$$\bar m_s(\alpha) = \sum_{z=1}^{\infty} u\Bigl(\bigl(1-\alpha(1-\delta)\bigr)^z - \delta^z\Bigr) = \frac{u\,(1-\alpha)}{(1-\delta)\,\alpha}.$$

**Clonal passengers.** The expected number of passengers acquired during the expansion that reach fraction one is

$$\bar m_c = \sum_{z=1}^{\infty} u\,\delta^z = \frac{\delta u}{1-\delta}.$$

**Allele-frequency form.** For heterozygous mutations in a diploid tumour (allele frequency $f$ equal to half the cell fraction) with no copy-number change, the expected number of mutations with allele frequency in $(f, 1/4)$ is

$$\frac{u}{2(1-\delta)}\left(\frac1f - \frac{1}{0.25}\right),$$

a $1/f$ law whose amplitude $u/(1-\delta)$ identifies only the ratio of mutation rate to $1-\delta$.

## Depends on

- [Eventual fraction of a passenger mutation in a birth–death expansion](eventual-fraction-of-a-passenger-mutation-in-a-birth-death-expansion.md)

## Expansion

At population size $z > 1$ the embedded jump chain moves up with probability $p = 1/(1+\delta)$, and a surviving mutation is produced before the next jump with probability $u(1-\delta)/(1+\delta)$; it is subclonal above $\alpha$ with probability $(1-\alpha(1-\delta))^z - \delta^z$. Writing $\bar m_k$ for the expected count starting from $k$ cells, the recursion $\bar m_k = u_k + p\bar m_{k+1} + (1-p)\bar m_{k-1}$ telescopes, with $\bar m_k \to 0$, to the displayed series, whose geometric sums give the closed forms. For $\delta$ near one the count of subclonal mutations above frequency $1/2$ is close to $\bar m_c$, and fitting the $1/f$ law to colorectal tumours with a normal exome mutation rate gives $\delta \approx 0.997$.

## Sources

- I. Bozic, J. M. Gerold, M. A. Nowak, "Quantifying clonal and subclonal passenger mutations in cancer evolution", PLoS Computational Biology 12 (2016) e1004731, Results Eqs (5)–(7) and Methods Eqs (37)–(46), <https://doi.org/10.1371/journal.pcbi.1004731> (PMC4734774).
