# Differences along a Trithoff row

Let $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{m+3} = T_{m+2} + T_{m+1} + T_m$ be the Tribonacci numbers, and for a finite word
$w = (w_0, \dots, w_{\ell-1})$ of natural-number digits, listed from the least significant
digit, let $[w]_T = \sum_{i=0}^{\ell-1} w_i T_{i+3}$ be its Tribonacci value. Let
$a = (a_0, \dots, a_{\ell-1})$ be a Tribonacci representation of a natural number $n$ (all
digits $0$ or $1$, no three consecutive ones, and $[a]_T = n$), and let
$b = (b_0, \dots, b_\ell)$ be the word with $b_i = a_i + a_{i-1}$, where $a_{-1} = a_\ell = 0$
(the product $11 \cdot a$ computed digit-wise without carries). For $k \ge 0$ write $0^k a$ for
the word $(0, \dots, 0, a_0, \dots, a_{\ell-1})$ with $k$ zeros placed before $a_0$, that is, at
the least significant end. Then there is a natural number $k$ with
$[0^{k+1} a]_T - [0^k a]_T = [b]_T$.

The entries of the Trithoff row of $n$ from $n$ onwards are $[0^k a]_T$ for $k \ge 0$, so
$[b]_T$ is the difference of two consecutive entries of that row.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Proposition 8 (`jis-2025-25.5.4-prop-8`).
