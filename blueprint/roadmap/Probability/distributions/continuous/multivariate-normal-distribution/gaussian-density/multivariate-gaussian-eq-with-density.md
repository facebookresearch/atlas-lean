# The multivariate Gaussian density

Let $\iota$ be a finite set of size $n$, let
$\mu \in \mathbb{R}^\iota$ and let $S$ be a positive definite real $\iota \times \iota$ matrix. Then
the multivariate Gaussian measure on the Euclidean space $\mathbb{R}^\iota$ with mean $\mu$ and
covariance matrix $S$ (the image of the standard Gaussian under $x \mapsto \mu + S^{1/2} x$) has
density

$$\frac{1}{(2\pi)^{n/2} \sqrt{\det S}} \exp\left(-\frac{(x - \mu)^\top S^{-1} (x - \mu)}{2}\right)$$

with respect to Lebesgue measure.
