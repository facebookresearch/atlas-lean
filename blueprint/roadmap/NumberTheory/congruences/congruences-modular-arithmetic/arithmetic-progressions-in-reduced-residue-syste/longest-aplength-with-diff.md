# Longest progression with a given common difference

For an integer $m$ and natural numbers
$n$ and $d$, let $R_m(n)$ be the set of integers $a$ with $m + 1 \le a \le m + n$ and
$\gcd(a, n) = 1$. Then $f_m(d, n)$ is the supremum of the natural numbers $s$ for which some
integer $b$ has $b + i d \in R_m(n)$ for every natural number $i < s$. For $d > 0$ every such $s$
is at most $n$, so $f_m(d, n)$ is the length of the longest arithmetic progression with common
difference $d$ contained in $R_m(n)$; the paper uses it only for $d > 0$, and for $d = 0$ the
definition gives $0$.

## Sources

- Phothila, Thoket and Kanasri, *Length of the Longest Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6, Section 2.
