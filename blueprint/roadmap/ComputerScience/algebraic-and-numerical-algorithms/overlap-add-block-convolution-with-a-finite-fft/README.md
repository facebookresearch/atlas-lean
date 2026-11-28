# Overlap-add block convolution with a finite FFT size

## Block partition

- [Number of overlap-add blocks](block-count.md)
- [Blocks of a signal](block.md)
- [The overlap-add blocks cover the signal](le-block-count-mul.md)
- [The last overlap-add block starts inside the signal](block-count-sub-one-mul-lt.md)
- [A block holds the signal inside the signal](block-apply-of-lt.md)
- [A block is zero past the end of the signal](block-apply-eq-zero-of-le.md)
- [Sample $n$ is entry $n \bmod L$ of block $\lfloor n/L \rfloor$](extend-nat-eq-block-div-mod.md)

## Block frames and overlap-add

- [Overlap-add block frame](block-frame.md)
- [Overlap-add](overlap-add.md)
- [Overlap-add frames by the discrete Fourier transform](block-frame-eq-inv-dft-mul.md)
- [Overlap-add block frames are linear convolutions](block-frame-eq-linear-convolution.md)
- [Overlap-add decomposition of linear convolution](linear-convolution-eq-sum-shifted-blocks.md)
- [Overlap-add computes the linear convolution](overlap-add-eq-linear-convolution.md)

## Boundary cases

- [Truncating overlap-add to the input length fails](truncation-to-input-length-fails.md)
- [Overlap-add with a short FFT size fails](overlap-add-ne-linear-convolution-of-sho.md)
- [Circular aliasing of overlap-add at a short FFT size](overlap-add-aliases-of-short-fft.md)
