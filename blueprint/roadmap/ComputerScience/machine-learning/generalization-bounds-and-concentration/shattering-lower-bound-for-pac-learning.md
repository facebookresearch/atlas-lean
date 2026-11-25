# Shattering lower bound for PAC learning

Let $m \ge 1$. If a class $\mathcal{H}$ of binary classifiers shatters a set of size $2m$, then no learning
algorithm that uses $m$ examples is a $(1/8, 1/7)$-PAC learner for $\mathcal{H}$ in the realizable setting:
for every such algorithm there is a distribution realizable by $\mathcal{H}$ on which, with probability at
least $1/7$, its output has error at least $1/8$. In particular, a class of infinite VC dimension is not
PAC learnable.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: No-free-lunch theorem.
- Statement prerequisite: Shattering and VC dimension.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Corollary 6.4. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
