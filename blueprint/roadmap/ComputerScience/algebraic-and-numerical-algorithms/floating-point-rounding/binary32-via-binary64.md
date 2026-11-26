# Binary32 arithmetic evaluated in binary64

Write $\mathrm{fl}_{p,q}$ for rounding to
nearest, ties to even, with $p$-bit significands, gradual underflow below the least exponent $q$
and unbounded exponent, so that $\mathrm{fl}_{24,-149}$ and $\mathrm{fl}_{53,-1074}$ are the
roundings of IEEE 754 binary32 and binary64 below overflow. For all real binary32 numbers $x$ and
$y$ (the numbers $m \cdot 2^e$ with $|m| < 2^{24}$ and $-149 \le e \le 104$), rounding the exact
sum, difference, product, quotient or square root to binary64 and then to binary32 gives the same
as rounding it directly to binary32: for $\circ \in \{+, -, \times, /\}$,
$\mathrm{fl}_{24,-149}(\mathrm{fl}_{53,-1074}(x \circ y)) = \mathrm{fl}_{24,-149}(x \circ y)$, and
$\mathrm{fl}_{24,-149}(\mathrm{fl}_{53,-1074}(\sqrt{x})) = \mathrm{fl}_{24,-149}(\sqrt{x})$.

For $y = 0$ and for $x < 0$ both sides of the statements for $x / y$ and $\sqrt{x}$ are $0$, with
the conventions $x / 0 = 0$ and $\sqrt{x} = 0$. Overflow is not modelled.
