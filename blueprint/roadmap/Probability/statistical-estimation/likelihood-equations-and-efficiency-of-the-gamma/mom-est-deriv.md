# Derivative matrix of the moment estimating function

A hyperparameter is a vector $\theta = (a, b) \in \mathbb{R}^2$ (prior shape $a$, prior rate $b$).
For a real size factor $\sigma$ and a count $k \in \mathbb{N}$, put

$$
D_\sigma(\theta, k) = \begin{pmatrix} -\sigma & k \\
-\sigma b - \sigma^2 - 2 \sigma^2 a & 2 b k^2 - \sigma a \end{pmatrix},
$$

acting on $\mathbb{R}^2$: the [derivative](has-fderiv-at-mom-est-fun.md) in $\theta$ of the
[moment estimating function](mom-est-fun.md) $g_\sigma(\theta, k)$.
