# Power series of the real exponential function

For every real $x$ the series $\sum_{k\ge0}x^k/k!$ converges absolutely, and

$$e^x=\sum_{k=0}^\infty\frac{x^k}{k!}.$$

In particular the partial sums $S_n(x)=\sum_{k=0}^{n}x^k/k!$ converge to $e^x$ as $n\to\infty$, and for $x\ge0$ they increase to $e^x$.

## Expansion

A proof page must establish absolute convergence by the ratio test, identify the sum with the exponential function as the library defines it (for instance as the solution of $y'=y$, $y(0)=1$, or as $\lim_n(1+x/n)^n$), and note that for $x\ge0$ every term is nonnegative, so the partial sums are nondecreasing.

## Sources

- W. Rudin, *Principles of Mathematical Analysis*, 3rd ed., McGraw-Hill, 1976, Chapter 8.
