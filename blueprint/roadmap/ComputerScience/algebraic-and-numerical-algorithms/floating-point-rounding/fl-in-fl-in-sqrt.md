# Innocuous double rounding of square roots with gradual underflow

Let $p \ge 1$ and
$p' \ge 2p + 2$ be natural numbers and let $q$, $q'$ and $q_{\max}$ be integers with
$q' \le q - p - 2$. Write $\mathrm{fl}_{p,q}$ for rounding to nearest, ties to even, with $p$-bit
significands, gradual underflow below the least exponent $q$ and unbounded exponent. For every real
number $x$ of the binary format with $p$-bit significands and last-place exponents in
$[q, q_{\max}]$, that is, $x = m_x 2^{e_x}$ for some integers with $|m_x| < 2^p$ and
$q \le e_x \le q_{\max}$ (this need not be the canonical exponent of the last place),
$\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(\sqrt{x})) = \mathrm{fl}_{p,q}(\sqrt{x})$.

For $x < 0$ both sides are $0$, with the convention $\sqrt{x} = 0$.
