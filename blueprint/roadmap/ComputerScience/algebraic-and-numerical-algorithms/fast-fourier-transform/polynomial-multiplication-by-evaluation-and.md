# Polynomial multiplication by evaluation and interpolation

A polynomial of degree less than $d$ over a field is determined by its values at any $d$ distinct points. Hence if $f$ and $g$ have degree less than $n$, evaluating both at $2n - 1$ distinct points, multiplying the values pointwise and interpolating yields $fg$. Over a field containing a primitive $N$-th root of unity $\omega$ where $N$ is the least power of two with $N \ge 2n - 1$, so that $N < 4n$, evaluation at the powers of $\omega$ and interpolation are the discrete Fourier transform and its inverse, which the fast Fourier transform computes in $O(N \log N)$ field operations; so $fg$ is computed in $O(n \log n)$ field operations.

## Proof depends on

- [FFT linear convolution returns the product polynomial (MIT/CLRS sign)](fft-polynomial-fft-linear-std-add-char-o.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Algebraic operation-count model (statement prerequisite; not yet stated)
- The statement must be checked against the cited sources, which have not been opened

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 4th ed., MIT Press, 2022
- J. Erickson, *Algorithms*, 1st ed., 2019, <https://jeffe.cs.illinois.edu/teaching/algorithms/>
