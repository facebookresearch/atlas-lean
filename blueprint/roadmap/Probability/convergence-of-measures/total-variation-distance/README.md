# Total variation distance

For finite measures $\mu$ and $\nu$ on a measurable space $\Omega$, the total variation distance is the real number $d_{\mathrm{TV}}(\mu, \nu) = \sup_B |\mu(B) - \nu(B)|$, the supremum over all measurable sets $B \subseteq \Omega$, with the masses $\mu(B)$ and $\nu(B)$ taken as real numbers. It is a metric on finite measures, and between probability measures it lies in $[0, 1]$.

## Idea

The total variation distance is the largest difference in probability that two laws can give to one event. If $\mu$ and $\nu$ have the same total mass (for instance, both are probability measures) and densities $f$ and $g$ against a common measure, the supremum is attained on $\{f > g\}$ and equals $\tfrac12 \int |f - g|$; for unequal masses it equals $\tfrac12 \big(\int |f - g| + |\mu(\Omega) - \nu(\Omega)|\big)$. In statistics, for probability measures, $1 - d_{\mathrm{TV}}(\mu, \nu)$ is the smallest possible sum of the two error probabilities of a test between $\mu$ and $\nu$. The metric is strong: when singletons are measurable, distinct point masses are at distance $1$, so the point masses at $1/n$ do not approach the point mass at $0$ in total variation, although they converge weakly.

## Statements

- [Total variation distance between finite measures](total-variation-dist.md)
- [Total variation distance is nonnegative](total-variation-dist-nonneg.md): basic property
- [Total variation distance from a measure to itself](total-variation-dist-self.md): basic property
- [Total variation distance vanishes only for equal measures](total-variation-dist-eq-zero-iff.md): basic property: it separates finite measures
- [Symmetry of total variation distance](total-variation-dist-comm.md): basic property: symmetry
- [Triangle inequality for total variation distance](total-variation-dist-triangle.md): basic property: triangle inequality
- [Total variation distance between probability measures is at most one](total-variation-dist-le-one.md): basic property for probability measures
- [Total variation distance between Dirac measures](total-variation-dist-dirac.md): example: Dirac measures

## Related topics

- [Total variation and Pinsker's inequality](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/README.md)
- [Strong data processing and Dobrushin's coefficient](../../../InformationTheory/information-inequalities/strong-data-processing-and-dobrushin-s-coefficie/README.md)
- [Differential privacy](../../../ComputerScience/cryptography/differential-privacy/README.md): for probability measures and a symmetric neighbouring relation, $(0, \delta)$-differential privacy says that the output laws on neighbouring databases are at total variation distance at most $\delta$; $(\varepsilon, \delta)$-privacy is the multiplicative refinement.
- [Wasserstein distances](../../../MeasureTheory/optimal-transport/wasserstein-distances/README.md):
  on a space of diameter $D$, the Wasserstein distance $W_1$ is at most $D$ times the total variation
  distance, and total variation is the optimal transport cost for the cost $1_{x \ne y}$.
- [Hellinger distance](../hellinger-distance/hellinger-dist.md): for probability measures $d_{\mathrm{TV}}/\sqrt2 \le d_{\mathrm{Hell}} \le d_{\mathrm{TV}}^{1/2}$, so the two distances define the same topology.
