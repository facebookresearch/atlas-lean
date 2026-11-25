# Optimal sample complexity of realizable PAC learning

For every nonempty class of binary classifiers with finite VC dimension $d$, there is a learning rule, a majority
vote of empirical risk minimizers trained on recursively constructed subsamples, that PAC learns the class in the
realizable setting with sample complexity

$$O\Big(\frac{d + \log(1/\delta)}{\varepsilon}\Big).$$

For $d \ge 2$ and $\varepsilon, \delta$ below absolute constants this matches, up to a constant factor, the lower bound
$\Omega\big((d + \log(1/\delta))/\varepsilon\big)$ for realizable PAC learning.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: VC classes have uniform convergence (upper half of the quantitative fundamental theorem).

## Proof depends on

- [Shattering lower bound for PAC learning](../generalization-bounds-and-concentration/shattering-lower-bound-for-pac-learning.md)

## Sources

- S. Hanneke, *The optimal sample complexity of PAC learning*, J. Mach. Learn. Res. 17 (2016); arXiv:1507.00473, Theorem 2 and §4.3. <https://arxiv.org/pdf/1507.00473>
- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 6.8 (lower bound). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
