# Convolution of the $(m-1)$-step and $m$-step Fibonacci numbers against powers of two

Write $F^{(m)}_n$ for the Fibonacci $m$-step numbers ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each
later term is the sum of the $m$ terms before it, terms at negative indices being $0$). For all
natural numbers $m \ge 2$ and $n \ge 2$,

$$\sum_{j=0}^{n} F^{(m-1)}_j F^{(m)}_{n-j} =
\sum_{j=0}^{n-2} 2^j \bigl(F^{(m-1)}_{n-1-j} - F^{(m)}_{n-2-j}\bigr).$$

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Theorem 12.
