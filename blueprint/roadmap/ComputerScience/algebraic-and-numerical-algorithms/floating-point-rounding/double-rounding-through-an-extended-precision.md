# Double rounding through an extended precision

Rounding an exact real result first to precision $p'$ and then to precision $p < p'$, both with round-to-nearest-even, can
differ from rounding it directly to precision $p$: with $p' = 64$ and $p = 53$, as on x87 hardware, the sum of $1$ and
$2^{-53} + 2^{-78}$ rounds directly to $1 + 2^{-52}$ but through 64 bits to $1$. In radix $2$ with unbounded exponents and
round-to-nearest at both precisions, double rounding is innocuous for all $p$-bit floating-point numbers $x$ and $y$:
$\mathrm{fl}_p(\mathrm{fl}_{p'}(x \pm y)) = \mathrm{fl}_p(x \pm y)$ if $p' \ge 2p + 1$; $\mathrm{fl}_p(\mathrm{fl}_{p'}(x \times y)) = \mathrm{fl}_p(x \times y)$ and,
for $y \ne 0$, $\mathrm{fl}_p(\mathrm{fl}_{p'}(x / y)) = \mathrm{fl}_p(x / y)$ if $p' \ge 2p$; and $\mathrm{fl}_p(\mathrm{fl}_{p'}(\sqrt{x})) = \mathrm{fl}_p(\sqrt{x})$
for $x \ge 0$ if $p' \ge 2p + 2$. Each bound is optimal. Formats with gradual underflow need further conditions on the two
minimum exponents; binary32 operations evaluated in binary64 and then rounded to binary32 meet them.

## Depends on

- [Round to nearest, ties to even](fl.md)
- [Binary floating-point numbers](is-float.md)

## Related topics

- [The relative error bound](abs-fl-sub-le.md)

## Sources

- Verified Compilation of Floating-Point Computations — S. Boldo, J.-H. Jourdan, X. Leroy, G. Melquiond, Journal of Automated Reasoning, Sec. 1 (x86 extended precision and the double-rounding example) and Sec. 3.2 (Figueroa's binary32/binary64 result). <https://xavierleroy.org/publi/floating-point-compcert.pdf>
- Innocuous Double Rounding of Basic Arithmetic Operations — P. Roux, Journal of Formalized Reasoning 7(1), 2014, Theorems 10, 20, 25 and 29 with Remarks 11, 21, 26 and 30 (after Figueroa, 1995), Tables I and II. <https://jfr.unibo.it/article/view/4359>
