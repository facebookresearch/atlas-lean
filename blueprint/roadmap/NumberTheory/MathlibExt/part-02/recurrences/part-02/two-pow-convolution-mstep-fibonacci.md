---
article_id: af_5932a794433c46d4ee2147f3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.two_pow_convolution_mstep_fibonacci
---

# MStep Fibonacci Convolution

Power-weighted convolution sum for Fibonacci m-step numbers: for `m ≥ 1`,
with `F 0 = 0`, `F 1 = 1`, and `F k = ∑_{j=1}^m F (k - j)` for `k ≥ 2`,
the sum `∑_{j=0}^n 2 ^ j * F (n - j)` equals `2 ^ (n + m - 1) - F (n + 1 + m)`.

The m-step initial conditions are the paper's definition (lines 126–133);
its negative-index values are 0, matching `F 0 = 0` under natural subtraction.
The paper states the theorem for `m ≥ 3`; the cases `m = 1, 2` also hold (checked
directly), so the hypothesis here is `1 ≤ m`.
Proves `Wanted` entry `two_pow_convolution_mstep_fibonacci`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.MStepFibonacciConvolution](../../../../../../sources/v2/MathlibExt.md)
- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci m-Step Numbers," Journal of Integer Sequences 27 (2024), Article 24.8.8, Theorem (label power2_conv), lines 453–459, https://cs.uwaterloo.ca/journals/JIS/VOL27/Gryszka/gryszka12.tex
