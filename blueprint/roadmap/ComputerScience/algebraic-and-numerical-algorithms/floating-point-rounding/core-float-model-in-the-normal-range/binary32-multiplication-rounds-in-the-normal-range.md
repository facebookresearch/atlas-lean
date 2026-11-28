# Binary32 multiplication rounds the exact product in the normal range

Let $a$ and $b$ be finite binary32 values, with any encoding including subnormals and signed zeros, representing rationals $x$ and $y$. If $2^{-126} \le |x y| \le (2^{24} - 1)\,2^{104}$, then the binary32 product $a b$ represents $\mathrm{fl}_{24}(x y)$, the rounding of $x y$ to 24 significant bits, to nearest with ties to even.

The bounds are the smallest normal and the largest finite binary32 numbers. Subnormal or overflowing results, infinities, NaNs and other rounding modes are outside the statement.

Here multiplication is `Float32.Model.mul` in Lean's core bit model; this is not a hardware-conformance claim.

## Depends on

- [Round to nearest, ties to even](../fl.md)

## Proof depends on

- [Round to nearest, ties to even](../fl.md)

Unfold the core operation and its rounding function. The normal-range bounds exclude exponent capping and special results, leaving the same ties-to-even rounding as $\mathrm{fl}_{24}$.

## Background

- [Binary64 multiplication rounds the exact product in the normal range](../../../not-yet-classified/float-model/to-rat-mul.md): the same statement for binary64.

## Sources

- Lean 4 core library, `Float32.Model` and its `mul` (`Init/Data/Float/Model/Float32.lean`, Lean v4.36.0), with the binary32 format parameters of `Init/Data/Float/Model/Format/Basic.lean`: 24-bit significand including the implicit bit, smallest normal $2^{-126}$, largest finite $(2^{24} - 1)\,2^{104}$.
- IEEE Std 754-2019, binary32 format.
