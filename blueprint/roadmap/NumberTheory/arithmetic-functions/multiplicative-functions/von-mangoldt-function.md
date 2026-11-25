# Von Mangoldt function

The *von Mangoldt function* is the function $\Lambda\colon \mathbb{N} \to \mathbb{R}$ given by $\Lambda(n) = \log p$ if $n = p^k$ for a prime $p$ and an integer $k \ge 1$, and $\Lambda(n) = 0$ otherwise. In particular $\Lambda(1) = 0$, and $\Lambda(0) = 0$ by convention.

## Sources

- Kenneth Ireland and Michael Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., Graduate Texts in Mathematics 84, Springer-Verlag, 1990.
- F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, https://dlmf.nist.gov/27.2#E14, equation 27.2.14 and the sentence following it, for positive integers n.
- The mathlib Community, *mathlib4* at revision 56a005855ea17e0b0958f73ec801ae140b0a1679, for the value at 0: `ArithmeticFunction.vonMangoldt`, https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean#L66-L67.
