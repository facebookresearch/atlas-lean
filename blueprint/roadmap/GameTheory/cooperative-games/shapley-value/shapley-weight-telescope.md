# Telescoping of the Shapley weights

For $1 \le k \le n$,

$$k\,w(n, k) - (n - k)\,w(n, k + 1) = \begin{cases} 1 & k = n, \\ 0 & k < n, \end{cases}$$

because both products equal $k!\,(n - k)!/n!$ when $k < n$. Summing Shapley's formula over the
players, the coefficient of $v(T)$ for a nonempty coalition $T$ is exactly this expression with
$k = |T|$, which is why the formula is efficient.

## Background

- [Shapley weight](shapley-weight.md): the weights compared.
