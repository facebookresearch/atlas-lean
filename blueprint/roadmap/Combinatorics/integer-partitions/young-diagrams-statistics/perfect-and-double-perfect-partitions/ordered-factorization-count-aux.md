# Truncated recursion for ordered factorizations

For natural numbers $k$ and $n$, define
$f_k(n)$ by recursion on $k$: $f_0(n) = 0$, $f_{k+1}(1) = 1$, and for $n \ne 1$, $f_{k+1}(n)$ is
the sum of $f_k(d)$ over the proper divisors $d$ of $n$, that is, the divisors $d$ of $n$ with
$1 \le d < n$ (there are none when $n = 0$).

## Sources

- Augustine O. Munagi, *Double Perfect Partitions of Higher Order*, INTEGERS 25 (2025), Article A109, Section 1 (definition of `f(n)`; summing over the first factor `n / d` of an ordered factorization gives the recursion).
