# Multivariate Gaussian density function

Let $\iota$ be a finite set of size $n$. For
$\mu, x \in \mathbb{R}^\iota$ and a real $\iota \times \iota$ matrix $S$, this is the real number

$$\frac{1}{(2\pi)^{n/2}\sqrt{\det S}} \exp\left(-\frac{(x - \mu)^\top S^{-1}(x - \mu)}{2}\right).$$

It is defined for every $S$, with the conventions $\sqrt{t} = 0$ for $t < 0$, $1/0 = 0$ and
$S^{-1} = 0$ for singular $S$, so its value is $0$ when $\det S \le 0$.
