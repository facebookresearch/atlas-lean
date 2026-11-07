# Church–Bicknell Fibonacci binomial convolution

For every natural number $n$,

$$\sum_{k=0}^{n} \binom{n}{k} F_k F_{n-k} = \frac{2^n L_n - 2}{5}$$

holds as an identity of rational numbers, where $F_k$ is the $k$-th Fibonacci number and $L_n$
is the $n$-th Lucas number.

## Sources

- Ira M. Gessel and Ishan Kar, "Binomial Convolutions for Rational Power Series," Journal of Integer Sequences 27 (2024), Article 24.1.3, equation `e-cb1` (attributed there to C. A. Church and Marjorie Bicknell, "Exponential generating functions for Fibonacci identities," Fibonacci Quarterly 11 (1973), 275–281). The proof follows the Binet-form computation in the JIS article: with `φ`, `ψ` the golden ratio and its conjugate, expand `(φ^k - ψ^k)(φ^(n-k) - ψ^(n-k))` and evaluate the four resulting binomial sums by the binomial theorem. Proves `Wanted` entry `church_bicknell_fibonacci_convolution`.
