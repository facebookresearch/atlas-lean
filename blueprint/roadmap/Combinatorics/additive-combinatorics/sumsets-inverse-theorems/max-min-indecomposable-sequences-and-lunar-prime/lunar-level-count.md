# Level counts of a lunar number

Let $f$ be a lunar number of base $b$ and degree at most
$n$, with digits $c_0, \dots, c_n \in \{0, \dots, b - 1\}$, and let $i$ be a natural number. The
level count $|f_i|$ is the number of indices $k \le n$ with $c_k \ge i$, that is, the number of
nonzero coefficients of the $i$-level support $f_i = s_i(f)$, the Boolean polynomial with
coefficient $1$ at $x^k$ when $c_k \ge i$ and $0$ otherwise.

A lunar number $f$ is not a monomial $t x^m$ (with $t = 0$ allowed) if and only if $|f_1| \ge 2$,
and $f_i$ is not a monomial if and only if $|f_i| \ge 2$.

## Sources

- Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2, Definitions 13 and 16.
