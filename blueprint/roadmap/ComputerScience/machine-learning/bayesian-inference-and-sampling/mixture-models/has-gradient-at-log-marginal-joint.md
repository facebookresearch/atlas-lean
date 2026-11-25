# The score of an isotropic Gaussian mixture with a common variance

Let $\theta$ be valid parameters of a $K$-component isotropic Gaussian mixture in $\mathbb{R}^d$
whose components all have the same variance $v$, with means $\mu_k$, mixture density $p_\theta$ and
responsibilities $r_k(x)$ (posterior component weights) at $x$. Then for every $x \in \mathbb{R}^d$,
the gradient of the log mixture density is
$\nabla \log p_\theta(x) = \big(\sum_k r_k(x)\, \mu_k - x\big) / v$.
