# Campbell's sequence $h_2$

For a natural number $n$, let $k = \lfloor \log_{10} n \rfloor$
(with $k = 0$ for $n = 0$), let $h_1$ be Campbell's sequence and let
$S_k = \sum_{i=1}^{10^k} h_1(i)$. Then
$h_2(n) = 10^k \lfloor S_k / 10^k \rfloor + \sum_{i=10^k+1}^{n} h_1(i)$, where the last sum is
empty when $n \le 10^k$.

This is OEIS A380904.

## Sources

- John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2, Equation (6) (definition of `h₂`).
