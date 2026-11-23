# Strong consistency of the rate MLE at a known shape

Let $\mu$ be a measure on $\Omega$ (in applications a probability measure) and let the counts
$X_0, X_1, \dots : \Omega \to \mathbb{N}$ be pairwise independent and identically distributed under
$\mu$, with $X_0$ integrable, with $\int X_0\, d\mu = \sigma a / b$ for some $\sigma, a, b > 0$, the
marginal mean of the hierarchy with size factor $\sigma$, shape $a$ and rate $b$. Let $M_n$ be the
[sample mean](count-mean.md) of $X_0, \dots, X_{n - 1}$. Then for $\mu$-almost every $\omega$, for
all large $n$ the rate $\hat b_n = \sigma a / M_n$ solves the [rate score](rate-score.md) equation
of the first $n$ counts at the common size factor $\sigma$ and the true shape $a$, and
$\hat b_n \to b$ as $n \to \infty$.
