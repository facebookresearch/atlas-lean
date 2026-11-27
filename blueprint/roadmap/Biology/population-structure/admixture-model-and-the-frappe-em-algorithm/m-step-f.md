# FRAPPE update of the allele frequencies

Let $I$ be finite. For a genotype matrix $g$, [admixture parameters](params.md) $\theta$, a population $k$ and a SNP $j$, the updated allele frequency is

$$F'_{kj} = \frac{R_{kj}(\theta)}{C_{kj}(\theta)},$$

where $R_{kj}$ is the [expected reference count](ref-count.md) and $C_{kj}$ the [expected population count](pop-count.md), with the convention $x/0 = 0$.
