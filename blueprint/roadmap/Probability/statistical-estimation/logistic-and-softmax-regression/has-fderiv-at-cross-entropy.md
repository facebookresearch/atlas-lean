# The gradient of the cross-entropy

For a finite nonempty set of classes $C$ with decidable equality, a label $y \in C$ and scores $z : C \to \mathbb{R}$, the cross-entropy $-\log \operatorname{softmax}(z)_y$ is differentiable in $z$ with gradient $\operatorname{softmax}(z) - e_y$, where $e_y$ is the indicator vector of $y$.
