# Total IEEE-style operation semantics with special values and exceptions

Let $F$ be a binary floating-point format with precision $p \ge 1$ and last-place exponents in $[q_{\min}, q_{\max}]$,
$q_{\min} \le q_{\max}$. Its value domain consists of the finite numbers $\pm m$, each given by a sign bit and a magnitude
$m \ge 0$ that is a number of the bounded format, so that $+0$ and $-0$ are distinct; the infinities $+\infty$ and
$-\infty$; and NaN. The model is canonical-NaN: all NaNs are identified, so a NaN carries neither a sign nor a payload,
and there is no signalling NaN. Let $r$ be one of the four rounding modes that IEEE 754-2019 requires for binary
arithmetic: round to nearest with ties to even, the default, or one of the three directed rounding modes, toward
$+\infty$, toward $-\infty$ and toward zero; round to nearest with ties away from zero, which the standard requires only
for decimal formats, is not modelled. Each basic operation ($+$, $-$, $\times$,
$\div$, $\sqrt{\ }$) is total: it returns a value of $F$ together with the status flags it raises, among invalid,
divide by zero, overflow, underflow and inexact.

- An operation with a NaN operand gives NaN and raises no flag.
- The invalid operations give NaN and raise the invalid flag: the addition of opposite infinities,
  $(+\infty) + (-\infty)$ and $(-\infty) + (+\infty)$; the subtraction of like infinities, $(+\infty) - (+\infty)$ and
  $(-\infty) - (-\infty)$; $0 \times \pm\infty$ and $\pm\infty \times 0$; $0 / 0$ and $\pm\infty / \pm\infty$, for zeros
  and infinities of either sign; and $\sqrt{x}$ for $x < 0$, $-\infty$ included.
- The division of a nonzero finite number by a zero gives the infinity whose sign is the exclusive or of the operands'
  signs, and raises the divide-by-zero flag.
- The other operations with an infinite operand give the exact infinite or zero result and raise no flag: a sum with
  an infinite operand is that infinity; a product with an infinite operand and no zero operand, and a quotient of an
  infinity by a finite number, a zero included, is the infinity whose sign is the exclusive or of the operands' signs;
  a finite number divided by an infinity is the zero of that sign; and $\sqrt{+\infty} = +\infty$.
- Otherwise the operands are finite, and the exact real result $x$ is rounded. If $x = 0$, the result is the zero whose
  sign the operation fixes: a sum of two zeros of the same sign is that zero, any other exact zero sum is $+0$, or $-0$
  when rounding toward $-\infty$; a product or quotient has the exclusive or of the operands' signs; and
  $\sqrt{\pm 0} = \pm 0$. If $x \ne 0$, let $y$ be $x$ rounded in mode $r$ at the last-place exponent
  $\max(\lfloor \log_2 |x| \rfloor - (p - 1), q_{\min})$, which rounds a result below the normal range to a multiple of
  $2^{q_{\min}}$, that is to zero, a subnormal number or the smallest normal number $\pm 2^{q_{\min} + p - 1}$
  (gradual underflow), and leaves the exponent unbounded above.
    - If $|y|$ exceeds the largest finite number $M = (2^p - 1) \cdot 2^{q_{\max}}$, the result overflows according to
      the mode, with the sign of $x$: it is $\pm\infty$ when rounding to nearest, $\pm M$ toward zero, $+\infty$ or
      $-M$ toward $+\infty$, and $+M$ or $-\infty$ toward $-\infty$. It raises the overflow and inexact flags.
    - Otherwise the result is $y$, a zero $y$ taking the sign of $x$. It raises the inexact flag if $y \ne x$, and the
      underflow flag if moreover $x$ is tiny, $|x| < 2^{q_{\min} + p - 1}$: tininess is detected before rounding, so a
      tiny result that rounds to $\pm 2^{q_{\min} + p - 1}$ still raises underflow, and an exact result raises no
      flag.

Subtraction $a - b$ is the addition of $a$ and $b$ with its sign bit flipped, so $(+\infty) - (-\infty) = +\infty$, and
$x - x = +0$ for a finite $x$, or $-0$ when rounding toward $-\infty$. In IEEE 754 the status flags are sticky; each
operation here returns only the flags it raises.

## Related topics

- [Four-outcome comparison](compare.md): NaN is unordered with every value, itself included, and $+0 = -0$.
- [`≤` is not a partial order with NaN](not-le-nan-and-not-is-partial-order.md), since $\mathrm{NaN} \le \mathrm{NaN}$
  fails.
- [Addition is commutative](eval-add-comm.md) and [multiplication is commutative](eval-mul-comm.md) in this canonical-NaN
  model, flags included.
- [Addition is not associative](not-add-assoc.md), in every format and rounding mode, and neither is
  [multiplication](not-mul-assoc.md) in a format with $q_{\min} \le -1$ and $q_{\max} \ge 1$, as for binary32 and
  binary64.
- [The relative error bound](abs-fl-sub-le.md)

## Sources

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019, Clause 4.3.3 (the rounding-direction attributes an implementation shall provide). <https://doi.org/10.1109/IEEESTD.2019.8766229>
- What Every Computer Scientist Should Know About Floating-Point Arithmetic — D. Goldberg, ACM Computing Surveys 23(1), 1991, Sec. 2.2 Special Quantities, Sec. 2.3 Exceptions, Flags, and Trap Handlers, and Sec. 3.2.2 IEEE Standard ($x - x = +0$ and the negation of zero). <https://www.cs.tufts.edu/comp/40/docs/WhatEveryComputerScientistShouldKnowAboutFloatingPointArithmetic.pdf>
- Verified Compilation of Floating-Point Computations — S. Boldo, J.-H. Jourdan, X. Leroy, G. Melquiond, Journal of Automated Reasoning 54(2), 2015, Sec. 5.1 (formats, signed zeros, infinities and NaN) and Sec. 5.2 (special cases first, then rounding with an exponent unbounded above, and the overflow result by rounding mode). <https://xavierleroy.org/publi/floating-point-compcert.pdf>
