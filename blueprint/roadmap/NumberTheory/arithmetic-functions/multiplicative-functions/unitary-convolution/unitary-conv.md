# Unitary convolution

Let $R$ be a semiring. The unitary convolution of two arithmetic
functions $f$ and $g$ with values in $R$ is the arithmetic function $f \sqcup g$ given by
$(f \sqcup g)(n) = \sum_{d \parallel n} f(d)\, g(n/d)$, where the sum runs over the unitary divisors
$d$ of $n$: for $n \ge 1$ these are the divisors $d$ of $n$ with $\gcd(d, n/d) = 1$, and $0$ has
no unitary divisors. In particular $(f \sqcup g)(0) = 0$.

## Sources

- Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7, Section 1.3.
