# Generating functions for ascending $k$-Naples parking functions

Let $I_{n,k}$ be the
number of weakly increasing $k$-Naples parking functions of length $n$, let $U_{n,k}$ be the
number of those whose first entry is $1$, and let $C_k$ be the $k$-th Catalan number. Write
$I_k(x) = \sum_{n \ge 0} I_{n,k} x^n$ and $U_k(x) = \sum_{n \ge 0} U_{n,k} x^n$, formal power
series with natural number coefficients. For every natural number $k \ge 1$,

$$I_k(x) = I_{k-1}(x) + C_k x^k I_{k-1}(x) U_k(x)$$

and

$$U_k(x) = U_{k-1}(x) + C_k x^k U_{k-1}(x) U_k(x).$$

## Sources

- J. P. Carvalho, P. E. Harris, G. Rojas Kirby, N. Tripeny and A. R. Vindas Meléndez, *Enumerating k-Naples Parking Functions through Catalan Objects*, INTEGERS 24 (2024), Article A44, Theorem 6.
