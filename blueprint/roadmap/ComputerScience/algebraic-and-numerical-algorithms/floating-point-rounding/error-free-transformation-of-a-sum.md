# Error-free transformation of a sum (TwoSum, FastTwoSum)

In binary floating-point arithmetic with round-to-nearest (unbounded exponents, or a bounded format with subnormals), for
floating-point numbers $a$ and $b$ such that no operation below overflows:

1. Knuth's TwoSum, $s = \mathrm{fl}(a + b)$, $b' = \mathrm{fl}(s - a)$, $a' = \mathrm{fl}(s - b')$,
   $e = \mathrm{fl}(\mathrm{fl}(a - a') + \mathrm{fl}(b - b'))$, returns $s = \mathrm{fl}(a + b)$ and a floating-point number $e$ with
   $s + e = a + b$ exactly;
2. Dekker's FastTwoSum, $s = \mathrm{fl}(a + b)$, $e = \mathrm{fl}(b - \mathrm{fl}(s - a))$, satisfies the same identity when
   $\lvert a \rvert \ge \lvert b \rvert$.

Both statements use the round-to-nearest model, not only a relative-error bound.

## Expansion

A good expansion adds a page for the following result, which this page does not state, and links it under the
dependency sections.

- Statement prerequisite: Dekker's FastTwoSum identity $s + e = a + b$ under the exponent condition
  $\lfloor \log_2 \lvert a \rvert \rfloor \ge \lfloor \log_2 \lvert b \rvert \rfloor$ for nonzero $a$ and $b$, in place of $\lvert a \rvert \ge \lvert b \rvert$.

## Depends on

- [Round to nearest, ties to even](fl.md)
- [Binary floating-point numbers](is-float.md)

## Proof depends on

- [The relative error bound](abs-fl-sub-le.md)
- [Floating-point subtraction is exact under Sterbenz's condition](fl-sub-eq-sub.md)

## Sources

- Accurate Sum and Dot Product — T. Ogita, S. M. Rump, S. Oishi, SIAM J. Sci. Comput. 26(6):1955-1988, 2005, DOI 10.1137/030601818, Sec. 1 eq. (1.1); Algorithm 1.1 (FastTwoSum, Dekker), Algorithm 3.1 (TwoSum, Knuth) and Theorem 3.4. <https://ogilab.w.waseda.jp/ogita/math/doc/2005_OgRuOi.pdf>
- Verified Compilation of Floating-Point Computations — S. Boldo, J.-H. Jourdan, X. Leroy, G. Melquiond, Journal of Automated Reasoning, Sec. 1 (Fast-Two-Sum for $\lvert a \rvert \ge \lvert b \rvert$). <https://xavierleroy.org/publi/floating-point-compcert.pdf>
