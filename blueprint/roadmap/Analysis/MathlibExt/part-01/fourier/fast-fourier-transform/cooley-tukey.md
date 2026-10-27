---
article_id: af_07aa174a8eadb79356ba5d51
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Fourier.FastFourierTransformWanted.cooley_tukey
---

# Cooley tukey

Radix-2 Cooley–Tukey splitting: a length-`2n` transform is two length-`n`
transforms on the even and odd subsequences plus twiddle factors.

Proof: Split the range into even and odd indices, rewrite the powers, and use
root-of-unity periodicity to reduce the frequency modulo `n`, as in the
section "The radix-2 DIT case" of Wikipedia, "Cooley–Tukey FFT algorithm".

## Depends on

- [Dft Sum](dft-sum.md)

## Proof depends on

- [Dft Sum mod](dft-sum-mod.md)
- [Dft Sum two mul](dft-sum-two-mul.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.FastFourierTransform](../../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Fourier transform", entry "fast Fourier transform"; J. W. Cooley and J. W. Tukey, Math. Comp. 19 (1965) (decimation in time).
