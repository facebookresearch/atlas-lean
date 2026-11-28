# Innocuous double rounding of quotients with gradual underflow

Let $K$ be a linearly ordered
field with a floor function, let $p \ge 1$ and $p' \ge 2p$ be natural numbers and let $q$, $q'$
and $q_{\max}$ be integers with $q' \le q - p - 2$. Write $\mathrm{fl}_{p,q}$ for rounding to
nearest, ties to even, with $p$-bit significands, gradual underflow below the least exponent $q$
and unbounded exponent. For all numbers $x, y \in K$ of the binary format with $p$-bit
significands and last-place exponents in $[q, q_{\max}]$, that is,
$x = m_x 2^{e_x}$ and $y = m_y 2^{e_y}$ for some integers with $|m_x|, |m_y| < 2^p$ and
$q \le e_x, e_y \le q_{\max}$ (these need not be the canonical exponents of the last place),
$\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(x / y)) = \mathrm{fl}_{p,q}(x / y)$.

For $y = 0$ both sides are $0$, with the convention $x / 0 = 0$.
