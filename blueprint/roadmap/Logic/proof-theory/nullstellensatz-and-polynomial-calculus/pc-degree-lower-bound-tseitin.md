# Polynomial calculus degree lower bound for Tseitin formulas

Let $G$ be a connected multigraph and $\chi$ a charge of odd total, and let $\mathbb{K}$ be a field of characteristic other than $2$. Every PC refutation of the clause polynomials of $T(G,\chi)$ with the Boolean axioms has degree at least $e(G)/2$, and the same bound holds for Nullstellensatz. On constant-degree expanders with edge expansion $h(G) > 0$ the degree is at least $h(G)|V|/6$, linear in the number of variables.

## Proof sketch

Change to the Fourier basis $y_e = 1 - 2x_e$, in which parity constraints become binomials; apply the invariant method with the space of polynomials whose low-degree part is reducible modulo the vertex constraints of small sets, using that sets with small edge boundary are smaller than a third of the vertices.

## Depends on

- [Tseitin formulas of a multigraph](../tseitin-formulas/tseitin-formulas-of-a-multigraph.md)
- [Polynomial calculus proofs, degree and size](polynomial-calculus-proofs.md)
- [Ben-Sasson–Wigderson expansion of a multigraph](../tseitin-formulas/balanced-cut-expansion.md)

## Proof depends on

- [The invariant method for polynomial calculus degree lower bounds](invariant-method-for-pc-degree.md)
- [Polynomial calculus simulates Nullstellensatz, and conversely without bounds](polynomial-calculus-simulates-nullstellensatz.md)

## Sources

- S. Buss, D. Grigoriev, R. Impagliazzo and T. Pitassi, "Linear Gaps between Degrees for the Polynomial Calculus Modulo Distinct Primes", Journal of Computer and System Sciences 62(2), 267–289, 2001.
- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001.
