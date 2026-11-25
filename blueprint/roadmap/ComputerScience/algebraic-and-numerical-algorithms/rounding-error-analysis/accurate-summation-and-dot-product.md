# Accurate summation and dot product (Sum2 / Dot2 / DotK)

This node collects the accurate summation and dot-product algorithms of Ogita, Rump and Oishi, each with its exact
error bound, in binary floating-point arithmetic with round-to-nearest, no overflow, and the underflow conventions of the
source.

## Expansion

A sound expansion has separate pages for:

1. **Sum2,** cascading TwoSum through the sum: $\lvert \mathrm{res} - s \rvert \le \varepsilon \lvert s \rvert + \gamma_{n-1}^2 \sum_i \lvert p_i \rvert$ with
   $\gamma_k = k\varepsilon/(1 - k\varepsilon)$, for $n\varepsilon < 1$, also with underflow.
2. **Dot2,** using TwoProduct and TwoSum: $\lvert \mathrm{res} - x^{\mathsf T} y \rvert \le \varepsilon \lvert x^{\mathsf T} y \rvert + \gamma_n^2 \lvert x^{\mathsf T} \rvert \lvert y \rvert$
   for $n\varepsilon < 1$ without underflow, plus $5n\eta$ with underflow, $\eta$ the underflow unit.
3. **DotK,** for $8n\varepsilon \le 1$: $\lvert \mathrm{res} - x^{\mathsf T} y \rvert \le (\varepsilon + 2\gamma_{4n-2}^2)\lvert x^{\mathsf T} y \rvert + \gamma_{4n-2}^K \lvert x^{\mathsf T} \rvert \lvert y \rvert$
   without underflow, plus $5n\eta$ with underflow.

Here $\varepsilon = 2^{-p}$ is the unit roundoff of precision $p$.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: the error bound of recursive floating-point summation, $\lvert \mathrm{fl}(\sum_{i \le n} a_i) - \sum_i a_i \rvert \le \gamma_{n-1} \sum_i \lvert a_i \rvert$, in any order and with underflow.

"As if computed in $K$-fold precision" describes the form of these bounds; it does not mean bitwise agreement with a
higher-precision computation.

## Depends on

- [The constant $\gamma_n$ of rounding error analysis](gamma.md)

## Proof depends on

- [Error-free transformation of a sum (TwoSum, FastTwoSum)](../floating-point-rounding/error-free-transformation-of-a-sum.md)
- [Error-free transformation of a product via fused multiply-add](../floating-point-rounding/error-free-transformation-of-a-product-via-fused-multiply-ad.md)

## Sources

- Accurate Sum and Dot Product — T. Ogita, S. M. Rump, S. Oishi, SIAM J. Sci. Comput. 26(6):1955-1988, 2005, DOI 10.1137/030601818, Sec. 1.2 and Sec. 2; Algorithm 4.4 and Proposition 4.5 (Sum2); Algorithm 5.3 and Proposition 5.5 (Dot2); Algorithm 5.10 and Proposition 5.11 (DotK). <https://ogilab.w.waseda.jp/ogita/math/doc/2005_OgRuOi.pdf>
