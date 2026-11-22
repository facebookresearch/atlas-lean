# Shifted power-weighted sums of k-Fibonacci numbers

Let $k$ be a nonzero integer and let
$F_{k,n}$ be the $k$-Fibonacci numbers, the Lucas sequence $U(k, -1)$: $F_{k,0} = 0$,
$F_{k,1} = 1$ and $F_{k,n+2} = k F_{k,n+1} + F_{k,n}$. Let $A_k^{(0)} = 1$ and
$A_k^{(p)} = \frac{2}{k} \sum_{j=1}^{\lceil p/2 \rceil} \binom{p}{2j-1} A_k^{(p-2j+1)}$ for
$p \ge 1$, and let $C_k^{(p)}(x) = \sum_{r=0}^{p} (-1)^r A_k^{(r)} \binom{p}{r} x^{p-r}$, with
$0^0 = 1$. Then for all natural numbers $m$, $n$ and $p$,

$$
k \sum_{i=1}^{n} i^p F_{k,m+i} = C_k^{(p)}(n) F_{k,m+n+1} + C_k^{(p)}(n+1) F_{k,m+n} -
C_k^{(p)}(0) F_{k,m+1} - C_k^{(p)}(1) F_{k,m}.
$$

The source takes $k$ to be a positive integer.

## Sources

- Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*, Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 11 (`jis-2024-24.6.4-thm-11`).
