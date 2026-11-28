# IEEE operations agree with rounding in the normal range

In the total IEEE-style semantics of a binary format with precision $p$ and last-place exponents in $[q_{\min}, q_{\max}]$, let $x$ and
$y$ be finite and let $\circ$ be one of $+$, $-$, $\times$, $\div$ with $y \ne 0$ for division. If the exact result $x \circ y$ lies in the
normal range of the format (its absolute value is at least the smallest normal number $2^{q_{\min} + p - 1}$ and at most the largest finite
number $(2^p - 1) \cdot 2^{q_{\max}}$), then, when rounding to nearest with ties to even, the value the operation returns is the finite
number $\mathrm{fl}(x \circ y)$, so it agrees with the rounding model of floating-point arithmetic. The statement concerns this value,
not the flags the operation also returns. Since the largest finite number is itself representable, an exact result of absolute value at most that number rounds to a finite number in every rounding mode, so no overflow occurs under this hypothesis; exact results beyond it are outside the statement, and IEEE 754 then decides overflow from the result rounded with an unbounded exponent range.

## Proof

Write $z = x \circ y$. For finite operands and a nonzero divisor, the operation delivers [the rounding of the exact result](round-result.md)
$z$, and $z \ne 0$, as $|z|$ is at least the smallest normal number. Rounding $z$ to nearest with ties to even
[in the bounded format](round.md) scales it at the last-place exponent $\max(e, q_{\min})$, where
$e = \lfloor \log_2 |z| \rfloor - (p - 1)$ is [the exponent of the last place](ulp-exp.md) of $z$.

- **The lower endpoint gives $q_{\min} \le e$.** From $2^{q_{\min} + p - 1} \le |z|$ follows
  $\lfloor \log_2 |z| \rfloor \ge q_{\min} + p - 1$, that is $e \ge q_{\min}$. So the clamp at $q_{\min}$ is inactive, no
  gradual-underflow rounding occurs, and the rounded value is $\mathrm{fl}_p(z)$.
- **The upper endpoint makes $\mathrm{fl}_p(z)$ representable.** The format has $p \ge 1$, and
  $2^{q_{\min} + p - 1} \le |z| \le (2^p - 1) \cdot 2^{q_{\max}}$, so [rounding stays in the format](is-float-in-fl.md):
  $\mathrm{fl}_p(z)$ is a number of the format. Its absolute value is therefore at most the
  [largest finite number](max-finite.md), the overflow branch does not apply, and the value returned is the finite number
  $\mathrm{fl}_p(z)$.

## Depends on

- [Total IEEE-style operation semantics with special values and exceptions](total-ieee-style-operation-semantics-with-special-values-and.md)
- [Floating-point numbers of a bounded format](is-float-in.md)
- [Round to nearest, ties to even](fl.md)
- [Largest finite number](max-finite.md)

## Proof depends on

- [Rounding an exact result](round-result.md)
- [Rounding in a bounded format](round.md)
- [Exponent of the last place](ulp-exp.md)
- [In the normal range, rounding stays in the format](is-float-in-fl.md)

## Sources

- D. Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1) (1991), Section 2 (the IEEE standard requires the result of each basic operation to be the exactly rounded result). <https://www.cs.tufts.edu/comp/40/docs/WhatEveryComputerScientistShouldKnowAboutFloatingPointArithmetic.pdf>
