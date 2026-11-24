# Total IEEE-style operation semantics with special values and exceptions

The value domain of a binary floating-point format consists of the finite numbers (with $+0$ and $-0$ distinct), $+\infty$,
$-\infty$ and NaN; whether NaN payloads are tracked or all NaNs are identified (canonical NaN) is part of the model. Each basic
operation ($+$, $-$, $\times$, $\div$, $\sqrt{\ }$) is total: the exact result is rounded in the current rounding mode when finite;
overflow gives $\pm\infty$ or the largest finite number according to the mode; results below the normal range are rounded to
subnormals (gradual underflow); invalid operations give NaN and raise the invalid flag; they are the addition of opposite infinities, $(+\infty) + (-\infty)$ and $(-\infty) + (+\infty)$, the subtraction of like infinities, $(+\infty) - (+\infty)$ and $(-\infty) - (-\infty)$, $0 \times \pm\infty$ and $\pm\infty \times 0$, $0/0$, $\pm\infty/\pm\infty$, and $\sqrt{x}$ for $x < 0$; an operation with
a NaN operand gives NaN; division of a nonzero finite number by zero gives an infinity with the sign rule; other operations
on infinities give the exact infinite result; and the status flags (invalid, divide by zero, overflow, underflow, inexact) are raised as specified. Comparison has four
outcomes (less, equal, greater, unordered), NaN is unordered with everything including itself, and $+0 = -0$; the relation
$\le$ is therefore not a partial order on a domain containing NaN, since $\mathrm{NaN} \le \mathrm{NaN}$ fails. Addition and
multiplication are commutative in a canonical-NaN model, and not associative.

## Depends on

- [Floating-point numbers of a bounded format](is-float-in.md)

## Related topics

- [The relative error bound](abs-fl-sub-le.md)

## Sources

- What Every Computer Scientist Should Know About Floating-Point Arithmetic — D. Goldberg, ACM Computing Surveys 23(1), 1991, Sec. 2.2 Special Quantities, Sec. 2.3 Exceptions, Flags, and Trap Handlers, and Sec. 3.2.3 Optimizers. <https://www.cs.tufts.edu/comp/40/docs/WhatEveryComputerScientistShouldKnowAboutFloatingPointArithmetic.pdf>
- Verified Compilation of Floating-Point Computations — S. Boldo, J.-H. Jourdan, X. Leroy, G. Melquiond, Journal of Automated Reasoning, Sec. 5.1 (formats, signed zeros, infinities, NaN with sign and payload) and Sec. 6.3 (unordered comparisons). <https://xavierleroy.org/publi/floating-point-compcert.pdf>
