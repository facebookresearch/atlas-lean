# Innocuous double rounding of products with gradual underflow

Let $K$ be a linearly ordered
field with a floor function, let $p$ and $p' \ge 2p$ be natural numbers and let $q$, $q'$ and
$q_{\max}$ be integers with $q' \le 2q$. Write
$\mathrm{fl}_{p,q}(z) = \operatorname{rne}(z / 2^e) \cdot 2^e$ with
$e = \max(\lfloor \log_2 |z| \rfloor - (p - 1), q)$, where $\operatorname{rne}$ rounds to the
nearest integer with ties to the even one; for $p \ge 1$, this is rounding to nearest, ties to
even, with $p$-bit significands, gradual underflow below the least exponent $q$ and unbounded
exponent. For all numbers $x, y \in K$ of the binary format with $p$-bit significands and
last-place exponents in $[q, q_{\max}]$,
$\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(xy)) = \mathrm{fl}_{p,q}(xy)$.

For $p = 0$ the format holds only $0$, so $x = y = 0$ and both sides are $0$.
