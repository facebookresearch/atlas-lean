# Scalar embedding preserves mutual information

Let $\iota : \mathbb{R} \to \mathbb{R}^1$, $x \mapsto (x)$, be the coordinate isometry onto one-dimensional Euclidean space. For a probability measure $\mu$ on $\mathbb{R} \times \mathbb{R}$ with marginals $\mu_1, \mu_2$, let

$$I(\mu) = \frac{D_{\mathrm{KL}}(\mu \,\|\, \mu_1 \otimes \mu_2)}{\log 2} \in [0, \infty]$$

be its mutual information in bits. Then $I\bigl((\iota \times \iota)_*\mu\bigr) = I(\mu)$, including when both sides are $\infty$.
