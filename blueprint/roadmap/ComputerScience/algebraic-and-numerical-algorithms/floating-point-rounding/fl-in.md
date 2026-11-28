# Round to nearest, ties to even, with gradual underflow

For a natural number $p$, an
integer $q$ and an element $x$ of a linearly ordered field with a floor function, let
$e = \max(\lfloor \log_2 |x| \rfloor - (p - 1), q)$: the exponent of the last place of $x$ at
precision $p$, but at least $q$. Let $\mathrm{fl}_{p,q}(x) = \operatorname{rne}(x / 2^e) \cdot 2^e$,
where $\operatorname{rne}$ rounds to the nearest integer with ties to the even one. For $p \ge 1$,
this is the rounding of $x$ to nearest, ties to even, in the binary format with $p$-bit
significands and least exponent $q$.

That format has gradual underflow: below $2^{q + p - 1}$ its numbers are the subnormal multiples
of $2^q$. Its exponent is unbounded above, so nothing overflows. For $p = 0$ the format holds only
$0$, and $\mathrm{fl}_{0,q}(x)$ need not be $0$.
