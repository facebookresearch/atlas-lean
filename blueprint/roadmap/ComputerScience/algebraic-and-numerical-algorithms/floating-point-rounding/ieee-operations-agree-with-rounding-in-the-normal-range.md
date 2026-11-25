# IEEE operations agree with rounding in the normal range

In the total IEEE-style semantics of a binary format, let $x$ and $y$ be finite and let $\circ$ be one of $+$, $-$, $\times$, $\div$ with
$y \ne 0$ for division. If the exact result $x \circ y$ lies in the normal range of the format (its absolute value is at least the smallest
normal number and at most the largest finite number), the operation returns $\mathrm{fl}(x \circ y)$, the exact result rounded in the
current rounding mode, so it agrees with the rounding model of floating-point arithmetic. Since the largest finite number is itself representable, an exact result of absolute value at most that number rounds to a finite number in every rounding mode, so no overflow occurs under this hypothesis; exact results beyond it are outside the statement, and IEEE 754 then decides overflow from the result rounded with an unbounded exponent range.

## Proof

When the exact result is finite and no invalid operation, division by zero or NaN operand occurs, the semantics specifies the
correctly rounded exact result; in the normal range no gradual-underflow branch applies.

## Depends on

- [Total IEEE-style operation semantics with special values and exceptions](total-ieee-style-operation-semantics-with-special-values-and.md)
- [Floating-point numbers of a bounded format](is-float-in.md)

## Sources

- D. Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1) (1991), Section 2 (the IEEE standard requires the result of each basic operation to be the exactly rounded result). <https://www.cs.tufts.edu/comp/40/docs/WhatEveryComputerScientistShouldKnowAboutFloatingPointArithmetic.pdf>
