# Uncorrelated jointly Gaussian random variables are independent

Let $P$ be a measure on a measurable space $\Omega$ and let $X, Y \colon \Omega \to \mathbb{R}$. Suppose that the pair
$(X, Y)$ has a Gaussian law under $P$: the map $\omega \mapsto (X(\omega), Y(\omega))$ is almost everywhere measurable,
and its image measure $\mu$ on $\mathbb{R}^2$ is Gaussian, meaning that for every continuous linear functional $L$ on
$\mathbb{R}^2$ the image of $\mu$ under $L$ is the normal distribution with mean $\int L \, d\mu$ and variance
$\operatorname{Var}_\mu(L)$ (the point mass at the mean when this variance is $0$). If the covariance

$$\operatorname{Cov}_P(X, Y) = \int_\Omega \big(X - \mathbb{E}_P[X]\big)\big(Y - \mathbb{E}_P[Y]\big) \, dP$$

is $0$, then $X$ and $Y$ are independent under $P$.
