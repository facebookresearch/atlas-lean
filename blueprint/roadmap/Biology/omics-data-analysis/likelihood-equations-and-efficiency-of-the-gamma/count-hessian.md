# Derivative matrix of the score of one count

A hyperparameter is a vector $\theta = (a, b) \in \mathbb{R}^2$ (prior shape $a$, prior rate $b$).
For a real size factor $\sigma$ and a count $k \in \mathbb{N}$, the score derivative matrix is the
symmetric matrix

$$
H_\sigma(\theta, k) = \begin{pmatrix} -\varphi_k(a) & 1/b - 1/(b + \sigma) \\
1/b - 1/(b + \sigma) & (a + k)/(b + \sigma)^2 - a/b^2 \end{pmatrix},
$$

acting on $\mathbb{R}^2$, with the [trigamma increment](trigamma-increment.md)
$\varphi_k(a) = \sum_{j < k} 1/(a + j)^2$ and the convention $0^{-1} = 0$. For $a, b > 0$ and
$\sigma \ge 0$ it is the [derivative](has-fderiv-at-count-score.md) of
$\theta \mapsto \psi_\sigma(\theta, k)$, the [score of one count](count-score.md); for $\sigma > 0$
it is therefore the Hessian of the log marginal likelihood of one count.
