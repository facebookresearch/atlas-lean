# Integral inequality for p-th powers with 0 < p < 1

Let $\mu$ be a measure and $0 < p < 1$. For all real-valued $f, g \in L^p(\mu)$,

$$\int \bigl| |f|^p - |g|^p \bigr| \, d\mu \le \int |f - g|^p \, d\mu.$$

## Idea

For $0 < p < 1$ the function $t \mapsto t^p$ on $[0, \infty)$ is concave and vanishes at $0$, so it
is subadditive: $(s + t)^p \le s^p + t^p$. Hence $\bigl| |a|^p - |b|^p \bigr| \le |a - b|^p$ for
all real $a$ and $b$, and integrating gives the inequality. It is the reason why, below exponent
$1$, the quantity $\int |f - g|^p \, d\mu$ itself, without a $p$-th root, is the natural distance
on $L^p$, and why $f \mapsto \int |f|^p \, d\mu$ is continuous for it.

## Statements

- [An integral inequality for $p$-th powers with $0 < p < 1$](integral-abs-rpow-sub-rpow-le-integral-r.md)
