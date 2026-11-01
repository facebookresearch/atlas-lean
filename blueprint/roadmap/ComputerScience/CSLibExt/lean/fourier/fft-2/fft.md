---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.TimeM.fft
---

# Fft

Radix-two FFT on `2^d` actual array entries, with supplied sample root.
The two transformed subsequences are stored once and combined with a running
twiddle. Root assumptions are needed for correctness, not for execution.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Fft Butterflies](fft-butterflies.md)
- [Fft Split](fft-split.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Fourier.FFT](../../../../../../sources/v2/CSLibExt.md)
