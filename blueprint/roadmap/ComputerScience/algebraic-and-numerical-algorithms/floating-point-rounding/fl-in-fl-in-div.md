# Innocuous double rounding of quotients with gradual underflow

Let $K$ be a linearly ordered
field with a floor function, let $p \ge 1$ and $p' \ge 2p$ be natural numbers and let $q$, $q'$
and $q_{\max}$ be integers with $q' \le q - p - 2$. Write $\mathrm{fl}_{p,q}$ for rounding to
nearest, ties to even, with $p$-bit significands, gradual underflow below the least exponent $q$
and unbounded exponent. For all numbers $x, y \in K$ of the binary format with $p$-bit
significands and last-place exponents in $[q, q_{\max}]$,
$\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(x / y)) = \mathrm{fl}_{p,q}(x / y)$.

For $y = 0$ both sides are $0$, with the convention $x / 0 = 0$.
