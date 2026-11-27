# Polynomial calculus resolution simulates resolution in degree $w+1$

Every resolution proof with $s$ lines and distinct-literal width at most $w$ translates into a PCR proof of the clause monomials of its lines, from the twin-variable encoding of the formula, of size $O(w \cdot s)$ and degree at most $w + 1$. Consequently resolution width $w$ implies PCR degree at most $w + 1$, and PCR polynomially simulates resolution.

## Proof sketch

A resolution step on $v$ from $A \vee v$ and $B \vee \neg v$ is simulated by multiplying the two clause monomials by the missing literal variables, giving $m_{A \vee B}\, x_{\bar v}$ and $m_{A \vee B}\, x_v$, adding them, and subtracting $m_{A \vee B}$ times the complementarity axiom $x_v + x_{\bar v} - 1$; each step uses $O(w)$ lines with at most three monomials each, all of degree at most $w + 1$.

## Depends on

- [Polynomial calculus proofs, degree and size](polynomial-calculus-proofs.md)
- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Sources

- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002: Section 4 (definition of PCR; simulation of resolution width by PCR degree).
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.5.3 and Figure 7.13.
- M. Clegg, J. Edmonds and R. Impagliazzo, "Using the Groebner Basis Algorithm to Find Proofs of Unsatisfiability", Proceedings of the 28th ACM Symposium on Theory of Computing (STOC), 1996.
