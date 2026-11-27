# Floating-point numbers of a bounded format

For a natural number $p$ and integers
$q_{\min}$ and $q_{\max}$, an element $x$ of a linearly ordered field with a floor function is a
number of the binary format with $p$-bit significands and last-place exponents in
$[q_{\min}, q_{\max}]$ when $x = m \cdot 2^e$ for some integers $m$ and $e$ with $|m| < 2^p$ and
$q_{\min} \le e \le q_{\max}$. These are zero, the subnormal numbers and the normal numbers of
the format.

In IEEE 754 terms, $q_{\min} = e_{\min} - p + 1$ and $q_{\max} = e_{\max} - p + 1$.
