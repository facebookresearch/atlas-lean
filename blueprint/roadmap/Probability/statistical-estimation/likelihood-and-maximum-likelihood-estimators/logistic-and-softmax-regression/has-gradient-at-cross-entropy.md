# Gradient of the cross-entropy

For a finite nonempty set of classes $C$ with decidable equality, a label $y \in C$ and scores $z \in \mathbb{R}^C$ with the Euclidean inner product, the gradient of the cross-entropy $-\log \operatorname{softmax}(z)_y$ at $z$ is $\operatorname{softmax}(z) - e_y$, where $e_y$ is the indicator vector of $y$.
