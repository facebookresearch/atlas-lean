# Smallest number at a given Matula height

Write $p_i$ for the $i$-th prime, indexed from
one ($p_1 = 2$), and let $H$ be a function from the natural numbers to themselves that is
completely additive on the positive integers and satisfies $H(p_i) = H(i) + 1$ for every $i \ge 1$
(Matula's height function). Then for every $n > 1$ the smallest positive integer $m$ with
$H(m) = n$ is $3 \cdot 5^{(n-2)/3}$ if $n \equiv 2 \pmod 3$, $5^{n/3}$ if $n \equiv 0 \pmod 3$, and
$9 \cdot 5^{(n-4)/3}$ if $n \equiv 1 \pmod 3$.

## Sources

- Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds, and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 6 (`integers-2026-A116-prop-6`).
