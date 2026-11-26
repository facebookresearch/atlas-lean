# The roundoff error of a floating-point sum is small and representable

Let $a$ and $b$ be binary floating-point numbers with $p$-bit significands and unbounded exponent, and write $\mathrm{fl}(a + b) = a + b + \mathrm{err}$ for rounding to nearest. Then

$$|\mathrm{err}| \le \min(|a|, |b|),$$

and $\mathrm{err}$ is itself a floating-point number with a $p$-bit significand. The same holds for subtraction. The proof uses only that $\mathrm{fl}(a + b)$ is a floating-point number closest to $a + b$, so the statements hold for any rule of breaking ties.

## Depends on

- [Round to nearest, ties to even](../fl.md)

## Sources

- J. R. Shewchuk, "Adaptive precision floating-point arithmetic and fast robust geometric predicates", *Discrete & Computational Geometry* 18(3):305–363, 1997; technical report version CMU-CS-96-140R, Section 2.2, Lemma 1 and Corollary 2 with their proofs. <https://people.eecs.berkeley.edu/~jrs/papers/robustr.pdf>
