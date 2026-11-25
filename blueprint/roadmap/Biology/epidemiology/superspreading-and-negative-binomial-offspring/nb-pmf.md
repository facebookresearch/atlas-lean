# Negative-binomial offspring probabilities

For real $R$ and $k$ and $n \in \mathbb{N}$, the negative-binomial offspring probability with mean $R$
and dispersion $k$ is

$$P_{R,k}(n) = \binom{k + n - 1}{n} \left(\frac{k}{k + R}\right)^{k} \left(\frac{R}{k + R}\right)^{n},$$

where $\binom{a}{n} = a(a - 1) \cdots (a - n + 1)/n!$ is the generalized binomial coefficient, the
first power is a real power (with $0^0 = 1$, $0^y = 0$ for $y \ne 0$, and $x^y = |x|^y \cos(\pi y)$ for
$x < 0$), and quotients by $k + R = 0$ are read as $0$ (Lloyd-Smith et al. 2005).
For $k > 0$ and $R \ge 0$ these are the probabilities of the negative-binomial law with mean $R$ and
dispersion $k$.
