# Square loss of a parametrized map

For a map $F : \mathbb{R}^P \to \mathbb{R}^n$ between Euclidean spaces, fixed targets $y \in \mathbb{R}^n$ and parameters $\theta \in \mathbb{R}^P$, the square loss is half the squared Euclidean distance between the outputs and the targets:

$$L_y(\theta) = \frac{1}{2} \sum_{i=1}^{n} \big(F(\theta)_i - y_i\big)^2 .$$
