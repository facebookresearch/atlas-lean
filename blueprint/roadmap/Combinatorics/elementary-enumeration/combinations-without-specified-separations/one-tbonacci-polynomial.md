# The $(1,t)$-bonacci polynomials

Fix a natural number $s$ and put $t = s + 1$. The
$(1,t)$-bonacci polynomials $f^{(t)}_n(x)$, $n \ge 0$, are the polynomials with natural-number
coefficients defined by $f^{(t)}_0(x) = 1$ and, for every $n \ge 0$,
$f^{(t)}_{n+1}(x) = f^{(t)}_n(x) + x \, f^{(t)}_{n-s}(x)$ if $s \le n$ and
$f^{(t)}_{n+1}(x) = f^{(t)}_n(x)$ if $n < s$.

Equivalently, $f^{(t)}_n(x) = f^{(t)}_{n-1}(x) + x \, f^{(t)}_{n-t}(x) + \delta_{n,0}$ with
$f^{(t)}_n(x) = 0$ for $n < 0$.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Section 3.2.
