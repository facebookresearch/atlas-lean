# Rounding an exact result

Let $F$ be a binary format with precision $p$ and exponent range
$[q_{\min}, q_{\max}]$, $r$ a rounding mode, $x$ a real number, the exact result of an operation
on finite operands, and $z$ the sign bit the operation gives an exact zero result. The value it
delivers, with the flags it raises, is:

* if $x = 0$, the zero of sign bit $z$, with no flag;
* otherwise let $y$ be $x$ rounded in mode $r$ in the bounded format (with gradual underflow and no
  upper bound on the exponent). If $|y|$ exceeds the largest finite number
  $(2^p - 1) \cdot 2^{q_{\max}}$, the result overflows: it is $\pm\infty$ in the mode to nearest,
  $\pm(2^p - 1) \cdot 2^{q_{\max}}$ toward zero, $+\infty$ or $-(2^p - 1) \cdot 2^{q_{\max}}$
  toward $+\infty$, and $+(2^p - 1) \cdot 2^{q_{\max}}$ or $-\infty$ toward $-\infty$, with the sign
  of $x$, and it raises the overflow and inexact flags;
* otherwise it is the number $y$ of the format, a zero $y$ taking the sign of $x$. It raises the
  inexact flag if $y \ne x$, and the underflow flag if moreover $x$ is tiny,
  $|x| < 2^{q_{\min} + p - 1}$: tininess is detected before rounding, and an exact tiny result
  raises no flag.

## Sources

- IEEE Std 754-2019; Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.3.2 (overflow by rounding mode); Boldo, Jourdan, Leroy and Melquiond, *Verified compilation of floating-point computations*, Journal of Automated Reasoning 54(2), 2015, Section 5.2.
