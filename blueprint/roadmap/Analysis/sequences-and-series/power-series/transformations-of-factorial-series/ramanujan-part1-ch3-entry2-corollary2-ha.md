# Ramanujan's series for the harmonic numbers, with Mathlib's harmonic numbers

Let
$H_k = \sum_{i=0}^{k-1} (i+1)^{-1}$ be Mathlib's $k$-th harmonic number. For every complex number
$x$, the series $\sum_{k \ge 1} \frac{H_k x^k}{k!}$ and
$\sum_{k \ge 1} \frac{(-1)^{k-1} x^k}{k!\, k}$ converge absolutely, and
$\sum_{k=1}^{\infty} \frac{H_k x^k}{k!} = e^x \sum_{k=1}^{\infty} \frac{(-1)^{k-1} x^k}{k!\, k}$.
