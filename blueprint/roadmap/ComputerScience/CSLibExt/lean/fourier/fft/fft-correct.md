---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.fft_correct
---

# DFTCorrectness

Every coefficient of the actual executed FFT is the complete source DFT sum.

## Depends on

- [Fft](../fft-2/fft.md)
- [Dft Sum](../../../../../Analysis/MathlibExt/part-01/fourier/fast-fourier-transform/dft-sum.md)

## Proof depends on

- [Fft Split](../fft-2/fft-split.md)
- [Fft Split ret even](correctness/fft-split-ret-even.md)
- [Fft Split ret odd](correctness/fft-split-ret-odd.md)
- [Fft ret succ high](correctness/fft-ret-succ-high.md)
- [Fft ret succ low](correctness/fft-ret-succ-low.md)
- [Fft ret zero](correctness/fft-ret-zero.md)
- [Cooley tukey](../../../../../Analysis/MathlibExt/part-01/fourier/fast-fourier-transform/cooley-tukey.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Fourier.FFT.DFTCorrectness](../../../../../../sources/v2/CSLibExt.md)
