---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.fft_time_add_one
---

# Fft time add one

The actual recursive run has cost `(7*d + 1)*2^d - 1`, including charged split/output writes.

## Depends on

- [Fft](../../fft-2/fft.md)

## Proof depends on

- [Fft Butterflies](../../fft-2/fft-butterflies.md)
- [Fft Butterflies time](fft-butterflies-time.md)
- [Fft Split](../../fft-2/fft-split.md)
- [Fft Split time](fft-split-time.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Fourier.FFT.Cost](../../../../../../../sources/v2/CSLibExt.md)
