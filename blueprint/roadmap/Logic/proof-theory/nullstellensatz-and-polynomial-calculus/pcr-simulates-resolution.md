# Polynomial calculus resolution simulates resolution in degree $w+1$

Every resolution proof with $s$ lines and distinct-literal width at most $w$ translates into a PCR proof of the clause monomials of its lines, from the twin-variable encoding of the formula, of size at most $(5w + 13)s$ and degree at most $w + 1$. Consequently resolution width $w$ implies PCR degree at most $w + 1$, and PCR polynomially simulates resolution.

## Proof sketch

A resolution step on $v$ from $A \vee v$ and $B \vee \neg v$ is simulated by multiplying the two clause monomials by the missing literal variables to reach the common monomial of $A \vee B$, and using the complementarity axiom for $v$ to cancel it; each step costs $O(w)$ monomials.

## Depends on

- [Polynomial calculus proofs, degree and size](polynomial-calculus-proofs.md)
- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

- [Polynomial calculus simulates Nullstellensatz, and conversely without bounds](polynomial-calculus-simulates-nullstellensatz.md)

## Sources

- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002.
- M. Clegg, J. Edmonds and R. Impagliazzo, "Using the Groebner Basis Algorithm to Find Proofs of Unsatisfiability", Proceedings of the 28th ACM Symposium on Theory of Computing (STOC), 1996.
