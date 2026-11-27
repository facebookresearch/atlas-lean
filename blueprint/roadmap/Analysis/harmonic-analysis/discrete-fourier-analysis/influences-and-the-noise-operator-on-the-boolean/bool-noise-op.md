# Noise operator on the Boolean cube

For a real number $\rho$ and a function $f$ from the
Boolean cube $\{-1, 1\}^n$ to $\mathbb{R}$, the noise operator $T_\rho$ sends $f$ to the function

$$T_\rho f(x) = \sum_y \Bigl(\prod_{i < n} \frac{1 + \rho \sigma(x_i) \sigma(y_i)}{2}\Bigr) f(y),$$

where $y$ runs over all points of the cube and $\sigma$ is the sign of a coordinate:
$\sigma(\mathrm{true}) = 1$ and $\sigma(\mathrm{false}) = -1$.

For $-1 \le \rho \le 1$, $T_\rho f(x)$ is the expectation of $f(y)$ when each coordinate of $y$
independently equals the corresponding coordinate of $x$ with probability $(1 + \rho) / 2$; the
formula is used for every real $\rho$.
