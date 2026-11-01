---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted.sum_trib_mul_tetra_eq
---

# Corollary 13

**Corollary 13**, fourth identity (corrected):
`∑_{j=0}^{n+2} T_j Q_{n+2-j} =
∑_{j=0}^n 2^j (T_{n+1-j} - Q_{n-j})`; the printed
`Q_{n-j}` on the left is a typo (the identity is Theorem
12 at `m = 4` with `n` replaced by `n + 2`; as printed it
fails at `n = 0`, giving `0` for `1`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.FibStepConvolutionWanted](../../../../../../../sources/v2/WantedExt.md)
- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Corollary 13.
