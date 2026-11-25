# Calculus of series-divisors

Let $R$ be a commutative ring, let $A$ be a formal power
series over $R$, write $[q^k]F$ for the coefficient of $q^k$ in a power series $F$, and let
$s : \mathbb{N} \to R$ satisfy $n\,[q^n]A = \sum_{i=1}^{n} s(i)\,[q^{n-i}]A$ for every $n \ge 0$
(that is, $s$ is a series-divisor of $A$). Then the following hold for every $n \ge 0$:
(a) for every power series $B$ over $R$ with $AB = 1$,
$n\,[q^n]B = \sum_{i=1}^{n} \bigl(-s(i)\bigr)\,[q^{n-i}]B$;
(b) $n\,[q^n]A(-q) = \sum_{i=1}^{n} (-1)^i s(i)\,[q^{n-i}]A(-q)$;
(c) for every integer $m \ge 1$, $n\,[q^n]A(q^m) = \sum_{i=1}^{n} t_m(i)\,[q^{n-i}]A(q^m)$,
where $t_m(i) = m\,s(i/m)$ if $m \mid i$ and $t_m(i) = 0$ otherwise;
(d) for every integer $m \ge 0$, $n\,[q^n]A^m = \sum_{i=1}^{n} m\,s(i)\,[q^{n-i}]A^m$.

## Sources

- Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Proposition 3 (`jis-2024-24.1.6-prop-3`).
