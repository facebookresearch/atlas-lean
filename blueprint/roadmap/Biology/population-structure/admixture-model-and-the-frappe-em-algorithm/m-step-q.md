# FRAPPE update of the ancestry proportions

Let $J$ be finite. For a genotype matrix $g$, [admixture parameters](params.md) $\theta$, an individual $i$ and a population $k$, the updated ancestry proportion is

$$Q'_{ik} = \frac{A_{ik}(\theta)}{2|J|},$$

where $A_{ik}$ is the [expected ancestry count](anc-count.md), with the convention $x/0 = 0$. For nonempty $J$ these are ancestry proportions (positive, summing to $1$ over $k$); for empty $J$ every updated value is $0$ by the convention.
