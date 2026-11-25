# VC dimension of sign-activation neural networks

For a fixed feedforward architecture with underlying graph $(V, E)$ and the sign activation function,
the class $\mathcal{H}_{V,E,\mathrm{sign}}$ of functions computed by the network with all choices of weights
has VC dimension $O(|E| \log |E|)$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: Sauer-Shelah-Perles lemma.
- Proof prerequisite: growth-function bounds for products and compositions of vector-valued function classes.

## Proof depends on

- [Feedforward network](backpropagation/net.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 20.6. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
