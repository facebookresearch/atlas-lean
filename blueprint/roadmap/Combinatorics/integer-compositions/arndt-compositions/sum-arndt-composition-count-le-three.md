# Arndt compositions with parts at most 3 and the Padovan numbers

For every $n \ge 0$, the
number of Arndt compositions of $n$ (compositions $(\sigma_1, \dots, \sigma_k)$ with
$\sigma_{2i-1} > \sigma_{2i}$ whenever $2i \le k$) with all parts in $\{1, 2, 3\}$, counting the
empty composition when $n = 0$, equals the shifted Padovan number $s_{n+2}$, where $s_0 = 1$,
$s_1 = 0$, $s_2 = 1$ and $s_{m+3} = s_{m+1} + s_m$. Equivalently, it is the Padovan number $P(n)$
given by $P(0) = P(1) = P(2) = 1$ and $P(n) = P(n-2) + P(n-3)$ for $n \ge 3$.

## Sources

- Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer Sequences 28 (2025), Article 25.3.6, Theorem 2 (`jis-2025-25.3.6-thm-2`).
