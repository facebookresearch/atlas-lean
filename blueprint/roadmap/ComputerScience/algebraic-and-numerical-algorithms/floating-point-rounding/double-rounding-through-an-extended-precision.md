# Double rounding through an extended precision

Write $\mathrm{fl}_p$ for rounding to nearest, ties to even, with $p$-bit significands and unbounded exponent, and call
a real number a $p$-bit floating-point number when it is $m \cdot 2^e$ for integers $m$ and $e$ with $|m| < 2^p$.
Rounding an exact real result first to precision $p'$ and then to precision $p < p'$ can differ from rounding it
directly to precision $p$: with $p' = 64$ and $p = 53$, as on x87 hardware, the sum of the 53-bit numbers $1$ and
$2^{-53} + 2^{-78}$ rounds directly to $\mathrm{fl}_{53}(1 + 2^{-53} + 2^{-78}) = 1 + 2^{-52}$, but through 64 bits
first to $\mathrm{fl}_{64}(1 + 2^{-53} + 2^{-78}) = 1 + 2^{-53}$, a tie at 53 bits, and then to
$\mathrm{fl}_{53}(1 + 2^{-53}) = 1$.

In radix $2$, with round-to-nearest-even at both precisions, double rounding is innocuous for every $p \ge 1$ and all
$p$-bit floating-point numbers $x$ and $y$:

- $\mathrm{fl}_p(\mathrm{fl}_{p'}(x \pm y)) = \mathrm{fl}_p(x \pm y)$ if $p' \ge 2p + 1$;
- $\mathrm{fl}_p(\mathrm{fl}_{p'}(x \times y)) = \mathrm{fl}_p(x \times y)$ if $p' \ge 2p$, and
  $\mathrm{fl}_p(\mathrm{fl}_{p'}(x / y)) = \mathrm{fl}_p(x / y)$ for $y \ne 0$ if $p' \ge 2p$;
- $\mathrm{fl}_p(\mathrm{fl}_{p'}(\sqrt{x})) = \mathrm{fl}_p(\sqrt{x})$ for $x \ge 0$ if $p' \ge 2p + 2$.

The bounds are optimal in these ranges of $p$: for every $p \ge 2$ there are $p$-bit floating-point numbers $x$ and
$y$ with $\mathrm{fl}_p(\mathrm{fl}_{2p}(x + y)) \ne \mathrm{fl}_p(x + y)$, others with
$\mathrm{fl}_p(\mathrm{fl}_{2p}(x - y)) \ne \mathrm{fl}_p(x - y)$, and others with $y \ne 0$ and
$\mathrm{fl}_p(\mathrm{fl}_{2p-1}(x / y)) \ne \mathrm{fl}_p(x / y)$; for every $p \ge 4$ there are such $x$ and $y$
with $\mathrm{fl}_p(\mathrm{fl}_{2p-1}(x \times y)) \ne \mathrm{fl}_p(x \times y)$; and for every $p \ge 1$ there is
such an $x \ge 0$ with $\mathrm{fl}_p(\mathrm{fl}_{2p+1}(\sqrt{x})) \ne \mathrm{fl}_p(\sqrt{x})$.

Formats with gradual underflow need further conditions on the two minimum exponents. Write $\mathrm{fl}_{p,q}$ for
rounding to nearest, ties to even, with $p$-bit significands, gradual underflow below the least exponent $q$, and
unbounded exponent: it sends $0$ to $0$ and rounds nonzero $x$ at the exponent
$\max(\lfloor \log_2 |x| \rfloor - (p - 1), q)$. For every $p \ge 1$,
all integers $q$, $q'$ and $q_{\max}$, and all real numbers $x$ and $y$ of the format with $p$-bit significands and
last-place exponents in $[q, q_{\max}]$, that is, $x = m_x 2^{e_x}$ and $y = m_y 2^{e_y}$ for some integers with
$|m_x|, |m_y| < 2^p$ and $q \le e_x, e_y \le q_{\max}$ (these need not be the canonical exponents of the last place),
double rounding through $\mathrm{fl}_{p',q'}$ is innocuous, that is,
$\mathrm{fl}_{p,q}(\mathrm{fl}_{p',q'}(r)) = \mathrm{fl}_{p,q}(r)$ for the exact result $r$: for $r = x \pm y$ if
$p' \ge 2p + 1$ and $q' \le q$, for $r = x \times y$ if $p' \ge 2p$ and $q' \le 2q$, for $r = x / y$ with $y \ne 0$ if
$p' \ge 2p$ and $q' \le q - p - 2$, and for $r = \sqrt{x}$ with $x \ge 0$ if $p' \ge 2p + 2$ and $q' \le q - p - 2$. For
the square root, Roux's Table II also gives the alternative condition $2q' \le q - 4p - 2$, which this statement does
not cover. Some condition on the minimum exponents is needed, even when the extended format contains the narrow one:
$16 = 2 \cdot 2^3$ and $3 = 3 \cdot 2^0$ are numbers of the format with $2$-bit significands and last-place exponents in
$[0, 3]$, yet $\mathrm{fl}_{2,0}(\mathrm{fl}_{4,0}(16 / 3)) = 4$ while $\mathrm{fl}_{2,0}(16 / 3) = 6$, although
$p' = 4 = 2p$ and $q' = q = 0$. Binary32 operations evaluated in binary64 and then rounded to binary32 meet the
conditions above, with $p = 24$, $q = -149$ and $q_{\max} = 104$ for binary32 and $p' = 53$ and $q' = -1074$ for
binary64: for all binary32 numbers $x$ and $y$,
$\mathrm{fl}_{24,-149}(\mathrm{fl}_{53,-1074}(x \circ y)) = \mathrm{fl}_{24,-149}(x \circ y)$ for
$\circ \in \{+, -, \times\}$, and likewise for $x / y$ when $y \ne 0$ and for $\sqrt{x}$ when $x \ge 0$.

## Proof sketch

Double rounding can differ from direct rounding only when the exact value is not a midpoint of consecutive $p$-bit
numbers but lies within half a last place of $p'$ bits of one. A product of two $p$-bit numbers has at most $2p$
significant bits, so it is exact at $p'$ bits. A sum is exact at $p'$ bits when both operands are multiples of the last
place of $p'$ bits of the sum. Otherwise one operand is $m \cdot 2^e$ with $|m| < 2^p$ and $2^e$ below that last place;
the other operand is then a multiple of the last place of $p$ bits of the sum, and the sum lies closer to it than half a
last place of $p$ bits minus half a last place of $p'$ bits. At the scale of its last place, a quotient is $N / m$ and a
square root is $\sqrt{N}$ for integers $N$ and $m$ with $|m| < 2^p$; so a quotient lies more than $2^{-p-1}$, and a
square root more than $2^{-p-3}$, last places from any midpoint other than itself, which half a last place of $p'$ bits
does not reach. With gradual underflow the sums and products are exact in the extended format or behave as above, and so
do quotients and square roots in the normal range of the narrow format. A quotient or square root that is subnormal
there is measured at the scale $2^q$ of its subnormal grid instead, where it need not have the form above: with $p = 3$
and $q = 0$, the quotient of $7$ and $16 = 4 \cdot 2^2$ is $7/16$ at that scale, whose denominator $16$ exceeds $2^p$,
and it lies exactly $2^{-p-1}$ from the midpoint $1/2$. Write $d$ for the number of binary places by which the last
place of the extended format lies below $2^q$; the conditions on $p'$ and $q'$ make $d$ at least $p + 1$ for a quotient
and $p + 2$ for a square root. A value that lies less than $1/2 - 2^{-d-1}$ from $0$ at that scale meets the criterion
with the representable number $0$. Otherwise its absolute value is at least $1/4$ there, and a square root, which is
positive, is at least $7/16$ there. A quotient is then $N / (4m)$ for integers $N$ and $m$ with $|m| < 2^p$, so it lies
more than $2^{-p-2}$ from any midpoint other than itself. A square root $M$ has $M^2 = m \cdot 2^s$ for integers $m$ and
$s$ with $0 < m < 2^p$, so unless $M$ is the nearest midpoint $n + 1/2$, $M^2$ differs from $(n + 1/2)^2$ by at least
$\min(1/4, 2^s)$, and $M$ still lies more than $2^{-p-3}$ from it. Half a last place of the extended format, $2^{-d-1}$
at that scale, reaches neither distance. The counterexamples generalise Figueroa's: for addition $x = 1 + 2^{1-p}$ and
$y = 2^{-p} - 2^{-2p}$, for division $x = 1$ and $y = 1 - 2^{-p}$, for the square root $x = 1 - 2^{-p}$, and for
multiplication $x = y = 13$ when $p = 4$ and $x = y = 3 \cdot 2^{p-2} - 1$ when $p \ge 5$.

## Related topics

- [The relative error bound](abs-fl-sub-le.md)

## Sources

- Verified Compilation of Floating-Point Computations — S. Boldo, J.-H. Jourdan, X. Leroy, G. Melquiond, Journal of Automated Reasoning, Sec. 1 (x86 extended precision and the double-rounding example) and Sec. 3.2 (Figueroa's binary32/binary64 result). <https://xavierleroy.org/publi/floating-point-compcert.pdf>
- Innocuous Double Rounding of Basic Arithmetic Operations — P. Roux, Journal of Formalized Reasoning 7(1), 2014, Theorems 10, 20, 25 and 29 with Remarks 11, 21, 26 and 30 (after Figueroa, 1995), Tables I and II. <https://jfr.unibo.it/article/view/4359>
