# Fisher information matrix of one count

For real $a$, $b$, $\sigma$ and $\tau$, the Fisher information matrix of one count is the symmetric
matrix

$$
I(a, b, \sigma, \tau) = \begin{pmatrix} \tau & -\sigma / (b (b + \sigma)) \\
-\sigma / (b (b + \sigma)) & a \sigma / (b^2 (b + \sigma)) \end{pmatrix},
$$

acting on $\mathbb{R}^2$, with the convention $x / 0 = 0$ in the entries. The shape entry $\tau$ is
a parameter. For $a, b > 0$, $\sigma \ge 0$, a count law with mean $\sigma a / b$ and $\tau$ the
expected [trigamma increment](trigamma-increment.md) $E[\varphi_K(a)]$, which has no closed form, it
is [minus the expected score derivative](integral-count-hessian.md).
