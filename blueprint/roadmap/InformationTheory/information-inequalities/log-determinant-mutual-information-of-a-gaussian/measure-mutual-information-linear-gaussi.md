# Mutual information of the Gaussian-input linear Gaussian channel

Let $\iota$ and $\kappa$ be finite index sets with $\iota$ nonempty, let $H \in \mathbb{R}^{\iota \times \kappa}$, let $K \in \mathbb{R}^{\kappa \times \kappa}$ be positive semidefinite (possibly singular) and let $R \in \mathbb{R}^{\iota \times \iota}$ be positive definite. On a probability space, let $X$ and $Z$ be measurable, independent, with $X \sim \mathcal{N}(0, K)$ on $\mathbb{R}^\kappa$ and $Z \sim \mathcal{N}(0, R)$ on $\mathbb{R}^\iota$, and let $Y = HX + Z$. Then

$$I(X; Y) = \frac{1}{2 \ln 2} \ln \frac{\det\left(R + H K H^{\mathsf{T}}\right)}{\det R} \text{ bits}.$$

Mutual information is measured in bits: the Kullback–Leibler divergence of the joint law from the product of its marginals, divided by $\ln 2$, with values in $[0, \infty]$.
