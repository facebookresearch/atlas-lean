# Moment estimating function of one count

A hyperparameter is a vector $\theta = (a, b) \in \mathbb{R}^2$ (prior shape $a$, prior rate $b$).
For a real size factor $\sigma$ and a count $k \in \mathbb{N}$, the moment estimating function is

$$
g_\sigma(\theta, k) = \bigl(b k - \sigma a,\quad
b^2 k^2 - \sigma a b - \sigma^2 a - \sigma^2 a^2\bigr).
$$

For $b \ne 0$, with $m = \sigma a / b$, it is
$\bigl(b (k - m),\ b^2 (k^2 - m - m^2 / a - m^2)\bigr)$, where $m^2 / a = 0$ for $a = 0$ by the
convention $x / 0 = 0$. For $a, b \ne 0$ the sample equations $\sum_i g_\sigma(\theta, k_i) = 0$ say
that the sample mean and second moment equal the negative binomial ones, $m$ and
$m + m^2 / a + m^2$; the [moment estimate](sum-mom-est-fun-mom-eq-zero.md) of an overdispersed
sample is a root.
