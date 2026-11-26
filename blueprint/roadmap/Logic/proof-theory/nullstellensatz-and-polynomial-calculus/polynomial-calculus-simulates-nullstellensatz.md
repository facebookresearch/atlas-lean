# Polynomial calculus simulates Nullstellensatz, and conversely without bounds

A Nullstellensatz certificate for a nonzero polynomial $q$ of size $s$ and degree $d$ yields a PC proof containing $q$ of size at most $s^2 + (d+1)s$ and degree at most $d$; in particular refutability in degree $d$ transfers from Nullstellensatz to PC. Conversely every line of a PC proof has a Nullstellensatz proof from the same inputs (with no degree or size bound). Hence PC degree is at most Nullstellensatz degree.

## Proof sketch

Expand each multiplier $g_i$ into monomials, derive each monomial multiple of $f_i$ by repeated multiplication by variables, and combine with linear combinations. Conversely, follow the PC rules: an input line has a unit multiplier, linear combinations combine multiplier families, and multiplication by a variable multiplies all multipliers.

## Depends on

- [Nullstellensatz proofs and degree](nullstellensatz-proofs.md)
- [Polynomial calculus proofs, degree and size](polynomial-calculus-proofs.md)

## Sources

- M. Clegg, J. Edmonds and R. Impagliazzo, "Using the Groebner Basis Algorithm to Find Proofs of Unsatisfiability", Proceedings of the 28th ACM Symposium on Theory of Computing (STOC), 1996.
- P. Beame, R. Impagliazzo, J. Krajíček, T. Pitassi and P. Pudlák, "Lower Bounds on Hilbert's Nullstellensatz and Propositional Proofs", Proceedings of the London Mathematical Society 73(1), 1–26, 1996.
