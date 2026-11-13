# Partial sums of the Fibonacci $m$-step numbers

For natural numbers $m \ge 2$ and $n$,
the Fibonacci $m$-step numbers $F^{(m)}_k$ satisfy

$$(m-1) \sum_{k=0}^{n} F^{(m)}_k =
F^{(m)}_{n+m} - \sum_{k=1}^{m-2} (m-1-k) F^{(m)}_{n+k} - 1.$$

The source prints this identity divided by $m - 1$ and with coefficients $k$ in place of
$m-1-k$; its proof gives $m-1-k$, and the printed form already fails at $m = 4$, $n = 1$, where
it gives $2/3$ instead of $1$.

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Theorem 8.
