# Binary64 fused multiply-add rounds the exact result once in the normal range

Let $a$, $b$ and $c$ be finite binary64 values, with any encoding including subnormals and signed zeros, representing rationals $x$, $y$ and $z$. If $2^{-1022} \le |x y + z| \le (2^{53} - 1)\,2^{971}$, then the binary64 fused multiply-add of $a$, $b$ and $c$ represents $\mathrm{fl}_{53}(x y + z)$, the rounding of the exact value $x y + z$ to 53 significant bits, to nearest with ties to even. In particular the product $x y$ is not rounded separately.

The bounds are the smallest normal and the largest finite binary64 numbers. Subnormal or overflowing results, infinities, NaNs and other rounding modes are outside the statement. It is a statement about one operation: error bounds for sums, dot products or factorizations evaluated without fused multiply-add do not cover code that contracts operations into it.

Here the fused operation is `Float.Model.fma` in Lean's core bit model; this is not a hardware-conformance claim.

## Depends on

- [Round to nearest, ties to even](../fl.md)

## Proof depends on

- [Round to nearest, ties to even](../fl.md)

Unfold the core fused operation. It forms the exact product plus addend before rounding; the normal-range bounds exclude exponent capping and special results, leaving $\mathrm{fl}_{53}$.

## Background

- [Binary64 addition rounds the exact sum in the normal range](../../../not-yet-classified/float-model/to-rat-add.md) and [binary64 multiplication rounds the exact product in the normal range](../../../not-yet-classified/float-model/to-rat-mul.md): the separately rounded operations.
- [Error-free transformation of a product via fused multiply-add](../error-free-transformation-of-a-product-via-fused-multiply-ad.md): a use of single rounding, stated in the bounded-format rounding model rather than for the core operation.

## Sources

- Lean 4 core library, `Float.Model.fma`, the fused multiply-add `a * b + c` with a single rounding (`Init/Data/Float/Model/Float.lean`, Lean v4.36.0).
- IEEE Std 754-2019, fusedMultiplyAdd.
