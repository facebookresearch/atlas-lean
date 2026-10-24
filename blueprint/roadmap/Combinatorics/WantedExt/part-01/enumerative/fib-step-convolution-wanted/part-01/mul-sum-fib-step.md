---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted.mul_sum_fibStep
---

# Theorem 8

**Theorem 8** (partial sums, corrected): for `m ≥ 2`,
`(m-1) ∑_{k=0}^n F⁽ᵐ⁾ₖ = F⁽ᵐ⁾_{n+m} -
∑_{k=1}^{m-2} (m-1-k) F⁽ᵐ⁾_{n+k} - 1`; the printed
coefficients `k` are a transcription error (the proof's
own display gives `m-1-k`; as printed the formula fails
already at `m = 4`, `n = 1`, giving `2/3` for `1`),
written multiplied through by `m - 1`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.FibStepConvolutionWanted](../../../../../../../sources/v2/WantedExt.md)
- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Theorem 8.
