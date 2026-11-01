---
article_id: af_841d246c6f0b3c99992a7277
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.church_bicknell_fibonacci_convolution
---

# Church bicknell fibonacci convolution

Church–Bicknell Fibonacci binomial convolution.

## Depends on

- [Lucas Number](../../part-07/lucas-sequence/lucas-number.md)

## Proof depends on

- [Cb key R](cb-key-r.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution](../../../../../sources/v2/MathlibExt.md)
- Ira M. Gessel and Ishan Kar, "Binomial Convolutions for Rational Power Series," Journal of Integer Sequences 27 (2024), Article 24.1.3, equation `e-cb1` (attributed there to C. A. Church and Marjorie Bicknell, "Exponential generating functions for Fibonacci identities," Fibonacci Quarterly 11 (1973), 275–281). The proof follows the Binet-form computation in the JIS article: with `φ`, `ψ` the golden ratio and its conjugate, expand `(φ^k - ψ^k)(φ^(n-k) - ψ^(n-k))` and evaluate the four resulting binomial sums by the binomial theorem. Proves `Wanted` entry `church_bicknell_fibonacci_convolution`.
