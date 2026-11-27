# Unnormalized Dirichlet density

For parameters
$\alpha = (\alpha_0, \dots, \alpha_n) \in \mathbb{R}^{n+1}$, the unnormalized Dirichlet density is
the function $D_\alpha \colon \mathbb{R}^n \to [0, \infty]$ defined by

$$D_\alpha(x) = \Bigl(\prod_{i=0}^{n-1} x_i^{\alpha_i - 1}\Bigr)
\Bigl(1 - \sum_{i=0}^{n-1} x_i\Bigr)^{\alpha_n - 1}$$

when $x$ lies in the open corner simplex, that is $x_i > 0$ for every $i$ and
$\sum_{i=0}^{n-1} x_i < 1$, and by $D_\alpha(x) = 0$ otherwise.

Here $x$ stands for the first $n$ coordinates of the probability vector
$(x_0, \dots, x_{n-1}, 1 - \sum_{i=0}^{n-1} x_i)$.
