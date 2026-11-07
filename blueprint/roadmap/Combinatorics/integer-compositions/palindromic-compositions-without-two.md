# Palindromic compositions without 2's

For an integer $m \ge 0$, let $C(m)$ be the number of
compositions of $m$ (finite sequences of positive integers with sum $m$) with no part equal to
$2$, so that $C(0) = 1$ counts the empty composition, and set $C(m) = 0$ for $m < 0$. For a
natural number $n$, let $P(n)$ be the number of such compositions of $n$ that are palindromes.
Then for every natural number $k$, $P(2k) = C(k+1)$ and $P(2k+1) = C(k+1) + C(k-1)$, and the
generating function $G_P(x) = \sum_{n \ge 0} P(n)\, x^n$ satisfies
$(1 - x^2 - x^3)\, G_P(x) = 1 + x$ as formal power series with integer coefficients.

The generating-function identity is the source's $G_P(z) = (1 + z)/(1 - z^2 - z^3)$ cleared of
denominators.

## Sources

- Phyllis Chinn and Silvia Heubach, "Integer Sequences Related to Compositions without 2's," Journal of Integer Sequences 6 (2003), Article 03.2.3, Theorem 10 (label `palnums`), lines 462–471, <https://cs.uwaterloo.ca/journals/JIS/VOL6/Heubach/heubach5.tex>.
