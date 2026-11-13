# Tribonacci representation

Let $T_n$ be the Tribonacci numbers, $T_0 = T_1 = 0$,
$T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$. A list $w = (w_0, \dots, w_{\ell-1})$ of
natural numbers, read least significant digit first, is a Tribonacci representation of a
natural number $n$ when every digit $w_i$ is $0$ or $1$, no three consecutive entries of $w$
are all equal to $1$, and $n = \sum_{i=0}^{\ell-1} w_i T_{i+3}$. Leading zeros (trailing
entries of $w$) are allowed.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Section 2.3 (Tribonacci representation).
