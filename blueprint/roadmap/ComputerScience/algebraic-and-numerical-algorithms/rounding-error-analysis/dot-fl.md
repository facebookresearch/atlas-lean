# Floating-point dot product

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent. For sequences $x, y$ in $K$, the floating-point dot product is the sequence

$$\hat s_0 = 0, \qquad \hat s_{k+1} = \mathrm{fl}\big(\hat s_k + \mathrm{fl}(x_k y_k)\big),$$

so that $\hat s_n$ is the value of $\sum_{i<n} x_i y_i$ obtained by rounding the products $x_i y_i$ and adding them from left to right, $i = 0, \dots, n - 1$, rounding each addition. For $n = 0$ the value is $0$.
