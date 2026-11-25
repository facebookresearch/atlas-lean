# Leave-one-out least squares: leverage and deleted residual

Let $X$ be a real design matrix with $m$ rows $x_1, \dots, x_m \in \mathbb{R}^\iota$ ($\iota$
finite), let $y \in \mathbb{R}^m$, assume that the Gram matrix $G = X^\top X$ is invertible, and fix
a row $i$ with leverage $h = x_i^\top G^{-1} x_i \ne 1$. Let $G_{-i} = G - x_i x_i^\top$ be the Gram
matrix without row $i$, $\beta = G^{-1} X^\top y$ the least-squares estimate, and
$\beta_{-i} = G_{-i}^{-1} (X^\top y - y_i x_i)$ the estimate without row $i$. Then:

- $G_{-i}$ is invertible;
- $\beta_{-i}$ is a least-squares estimate of the data with row $i$ deleted: it minimizes the
  residual sum of squares of the design and responses with row $i$ set to zero, which is
  $\sum_{k \ne i} (y_k - x_k^\top \theta)^2$;
- $q = x_i^\top G_{-i}^{-1} x_i$ satisfies $q = h / (1 - h)$ and $h = q / (1 + q)$;
- the residuals $e_i = y_i - x_i^\top \beta$ and $e_{-i} = y_i - x_i^\top \beta_{-i}$, both at the
  original row $i$, satisfy $e_i = (1 - h) e_{-i}$.
