# Measure Mutual Information dirac comp Prod noise Kernel le

Let $\iota$ and $\kappa$ be finite index sets with $\iota$ nonempty, $H \in \mathbb{R}^{\iota \times \kappa}$, $R \in \mathbb{R}^{\iota \times \iota}$ positive definite, and $c \in \mathbb{R}^\kappa$ arbitrary. Let $N_H$ be the Gaussian noise kernel sending $x$ to the law of $Hx + Z$ with $Z \sim \mathcal{N}(0, R)$. For the input fixed at $c$ (the point mass $\delta_c$, with covariance $0$), the mutual information in bits satisfies the converse bound at $K = 0$:

$$I(\delta_c \otimes N_H) \le \max\left\{\frac{1}{2\ln 2}\ln\frac{\det(R + H \cdot 0 \cdot H^\top)}{\det R},\ 0\right\} = 0.$$
