# Multilinear extension

Let $f$ be a Boolean-valued function on the Boolean cube of
dimension $n$, and read each coordinate and each value as $1$ for true and $0$ for false. The real
multilinear extension of $f$ is the polynomial in $\mathbb{R}[X_0, \dots, X_{n-1}]$

$$\sum_{x \in \{0,1\}^n} f(x) \prod_{i < n} \bigl(x_i X_i + (1 - x_i)(1 - X_i)\bigr).$$

For each cube point $x$ the product is its Lagrange basis polynomial: it evaluates to $1$ at $x$
and to $0$ at every other point of $\{0,1\}^n$. Hence the extension agrees with $f$ on
$\{0,1\}^n$, and it is the unique polynomial of degree at most one in each variable that does.
