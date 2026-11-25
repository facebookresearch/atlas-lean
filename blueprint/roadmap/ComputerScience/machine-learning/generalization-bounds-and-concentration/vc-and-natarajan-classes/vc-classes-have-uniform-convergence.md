# VC classes have uniform convergence (upper half of the quantitative fundamental theorem)

Let $H \subseteq \{0,1\}^X$ have $\mathrm{VCdim}(H) = d < \infty$, with the measurability needed for symmetrization, under 0-1
loss. There is an absolute constant $C$ such that $H$ has the uniform convergence property with
$m^{UC}_H(\varepsilon, \delta) \le \lceil C (d + \log(2/\delta))/\varepsilon^2 \rceil$ for all $\varepsilon, \delta \in (0,1)$, including
$d = 0$. Consequently the agnostic PAC sample complexity is $O((d + \log(1/\delta))/\varepsilon^2)$ and the realizable
PAC sample complexity is $O((d \log(1/\varepsilon) + \log(1/\delta))/\varepsilon)$, as separate corollaries. The
symmetrization and Sauer–Shelah lemmas are proof prerequisites.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: VC dimension of a class of binary functions.

- Proof prerequisite: Sauer-Shelah-Perles lemma.
- Proof prerequisite: Ghost-sample symmetrization.

## Depends on

- [Uniform convergence property and eps-representative samples](../../pac-learning/agnostic-pac-learning-and-uniform-convergence/uniform-convergence-property-and-eps-representative-samples.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 6.8 (quantitative fundamental theorem: the uniform-convergence, agnostic and realizable sample complexities), whose upper bounds are proved in Chapter 28; Section 28.1 proves a bound with an extra logarithmic factor and notes that the sharp rate needs chaining. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
