---
article_id: af_ad840d0220e4efe693ad661b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Fourier.FastFourierTransformWanted.fftCost_recurrence
---

# Fft Cost recurrence

The `n log n` cost satisfies the radix-2 FFT recurrence.

Proof: Apply `Nat.log_mul_base` to `n * 2`, commute the factors, and expand
multiplication.

## Depends on

- [Fft Cost](fft-cost.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.FastFourierTransform](../../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Fourier transform", entry "fast Fourier transform"; J. W. Cooley and J. W. Tukey, Math. Comp. 19 (1965) (`n log n` operation count).
