# Convolution of the Fibonacci numbers with tribonacci minus tetranacci

Write $F_n$, $T_n$
and $Q_n$ for the Fibonacci, tribonacci and tetranacci numbers, that is, the Fibonacci $m$-step
numbers $F^{(m)}_n$ for $m = 2, 3, 4$ ($F^{(m)}_0 = 0$, $F^{(m)}_1 = 1$, and each later term is the
sum of the $m$ terms before it, terms at negative indices being $0$). For every natural number
$n \ge 1$,

$$\sum_{j=0}^{n} F_j (T_{n-j} - Q_{n-j}) = \sum_{j=0}^{n-1} (F_j - T_j) Q_{n-1-j}.$$

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Corollary 11.
