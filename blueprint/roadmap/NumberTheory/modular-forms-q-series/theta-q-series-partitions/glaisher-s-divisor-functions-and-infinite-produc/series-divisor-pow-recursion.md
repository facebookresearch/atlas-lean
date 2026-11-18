# Coefficient recursion for powers of a power series

Let $R$ be a commutative ring, let
$A$ be a formal power series over $R$ with coefficients $a(k)$, and let $s : \mathbb{N} \to R$
satisfy $k\,a(k) = \sum_{i=1}^{k} s(i)\,a(k-i)$ for every $k \ge 0$ (that is, $s$ is a
series-divisor of $A$). For natural numbers $m$ and $k$, write $a_m(k)$ for the coefficient of
$q^k$ in $A^m$. Then for all natural numbers $m$ and $n$,
$n\,a_m(n) = m \sum_{j=1}^{n} s(j)\,a_m(n-j)$.

The source writes the series-divisor $s$ as $\sigma^A$ and prints the summand with $\sigma^A(i)$;
it is read as $\sigma^A(j)$, with the summation index $j$.

## Sources

- Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Corollary 4 (`jis-2024-24.1.6-cor-4`).
