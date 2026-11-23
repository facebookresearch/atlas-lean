# Jacobian of the moment equations

For real $a$, $b$ and $\sigma$, the moment Jacobian is the matrix

$$
J(a, b, \sigma) = \begin{pmatrix} -\sigma & \sigma a / b \\
-\sigma b - \sigma^2 - 2 \sigma^2 a & \sigma a + 2 \sigma^2 a (1 + a) / b \end{pmatrix},
$$

acting on $\mathbb{R}^2$, with the convention $x / 0 = 0$. For $b \ne 0$ its determinant is
$-\sigma^3 a / b$. For $a, b > 0$ and a count law with the negative binomial mean and second moment
it is the [expected derivative](integral-mom-est-deriv.md) of the moment estimating function at
$(a, b)$.
