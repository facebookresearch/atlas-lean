# Binary floating-point format

A binary format has a precision $p \ge 1$ (the number of
significand bits) and integers $q_{\min} \le q_{\max}$, the least and greatest exponents of the
last place. Its finite numbers are the numbers of the bounded format: $m \cdot 2^e$ with integers
$|m| < 2^p$ and $q_{\min} \le e \le q_{\max}$, which are zero, the subnormal numbers and the
normal numbers. In IEEE 754 terms, $q_{\min} = e_{\min} - p + 1$ and
$q_{\max} = e_{\max} - p + 1$; binary64 has $p = 53$, $q_{\min} = -1074$ and $q_{\max} = 971$.

## Sources

- IEEE Std 754-2019; Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.1 (Table 1).
