# The von Mangoldt function summed over the divisors of a positive integer n gives log n

Let $\Lambda$ be the von Mangoldt function, so $\Lambda(m) = \log p$ if $m = p^k$ for a prime $p$ and an integer $k \ge 1$, and $\Lambda(m) = 0$ otherwise. Then for every positive integer $n$,

$$\sum_{d \mid n} \Lambda(d) = \log n,$$

where the sum runs over the positive divisors $d$ of $n$. Mathlib states this as the identity $\Lambda * \zeta = \log$ of arithmetic functions, where $*$ is Dirichlet convolution and $\zeta$ is the arithmetic zeta function, equal to $1$ at every positive integer, not the Riemann zeta function. Mathlib's arithmetic functions are functions on the natural numbers that take the value $0$ at $0$; for the logarithm this is Mathlib's convention $\log 0 = 0$. So the identity holds at every natural number $n$: at $n = 0$ both sides are $0$, and at a positive integer $n$ it is the divisor-sum identity above.

## Sources

- Tom M. Apostol, Introduction to Analytic Number Theory, Undergraduate Texts in Mathematics, Springer-Verlag, 1976, §2.8, Theorem 2.10, p. 32.
- F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, https://dlmf.nist.gov/27.5#E5, equation 27.5.5, first identity, for positive integers n.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the convolution with the arithmetic zeta function as a divisor sum: `ArithmeticFunction.coe_mul_zeta_apply`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ArithmeticFunction/Zeta.lean#L87-L89.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for arithmetic functions taking the value 0 at 0 and the logarithm as an arithmetic function: `ArithmeticFunction`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean#L48-L51, and `ArithmeticFunction.log`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean#L47-L54.
