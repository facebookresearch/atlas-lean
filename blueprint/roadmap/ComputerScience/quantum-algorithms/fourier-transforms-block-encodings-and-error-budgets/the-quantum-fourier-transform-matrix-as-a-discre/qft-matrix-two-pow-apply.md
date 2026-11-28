# Product formula for the 2^n-point quantum Fourier transform

For `k j : Fin (2 ^ n)`, the entry of the `2 ^ n`-point quantum Fourier
transform matrix factors over the bits of the row index: `qftMatrix (2 ^ n)
k j` is the product over `l < n` of `(√2)⁻¹` times `exp (2πi j / 2 ^ (n -
l))` if bit `l` of `k` is `1`, and `(√2)⁻¹` otherwise.

Here `qftMatrix q` is the `q × q` complex matrix with entries `qftMatrix q j
k = (√q)⁻¹ exp (2πi j k / q)`.
