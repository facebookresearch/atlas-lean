# Polynomial calculus proofs, degree and size

A *polynomial calculus* (PC) proof from inputs $F$ over a field $\mathbb{K}$ is a sequence of polynomials in which each line is an input, a linear combination $\alpha p + \beta q$ of two earlier lines, or $x_i \cdot p$ for an earlier line $p$ and a variable $x_i$. It refutes $F$ if it contains the constant $1$. Its *degree* is the maximum total degree of a line and its *size* the total number of monomials over all lines. *Polynomial calculus resolution* (PCR) is PC on the twin-variable encoding, with the Boolean and complementarity axioms as inputs. PC proofs are sound: every line vanishes at every common zero of the inputs.

## Depends on

- [Boolean axioms and CNF arithmetization](boolean-axioms-and-cnf-arithmetization.md)

## Sources

- M. Clegg, J. Edmonds and R. Impagliazzo, "Using the Groebner Basis Algorithm to Find Proofs of Unsatisfiability", Proceedings of the 28th ACM Symposium on Theory of Computing (STOC), 1996.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.5.2 (rules (7.20a)–(7.20d) and the size and degree measures).
- M. Alekhnovich, E. Ben-Sasson, A. A. Razborov and A. Wigderson, "Space Complexity in Propositional Calculus", SIAM Journal on Computing 31(4), 1184–1211, 2002.
