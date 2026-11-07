# Borwein's eta–Lambert correspondence

Let $(a_n)$ and $(b_n)$ be sequences of complex
numbers and let $C$ and $K$ be real numbers with $|a_n| \le C n^K$ and $|b_n| \le C n^K$ for every
$n \ge 1$. Let $\eta(s) = \sum_{n \ge 1} (-1)^{n-1} n^{-s}$ be the Dirichlet eta function. Then
$\eta(s) \sum_{n \ge 1} a_n n^{-s} = \sum_{n \ge 1} b_n n^{-s}$ for every real number
$s > \max(K + 2, 1)$ if and only if $\sum_{n \ge 1} a_n x^n / (1 + x^n) = \sum_{n \ge 1} b_n x^n$
for every real number $x$ with $0 < x < 1$.

The source quotes the correspondence from Borwein and Borwein without growth hypotheses or
ranges for $s$ and $x$; the growth bound and the ranges above make all the series involved converge
absolutely.

## Sources

- Christophe Vignat and Michael Milgram, *Curious Multisection Identities by Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 18 (`jis-2024-24.5.5-prop-18`).
