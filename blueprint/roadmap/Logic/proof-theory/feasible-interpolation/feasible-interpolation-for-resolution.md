# Feasible interpolation for resolution

If $A(x, y) \wedge B(x, z)$ has a resolution refutation with $s$ lines, then it has an interpolant computed by a De Morgan circuit with at most $4s$ gates. If moreover the shared variables occur only positively in $A$ (or only negatively in $B$), then it has a monotone interpolant computed by a monotone circuit with at most $2s$ gates. The circuit is computable from the refutation in polynomial time.

## Proof sketch

Assign a gate to each line: constant $0$ to clauses of $A$, constant $1$ to clauses of $B$; for a resolvent on a variable private to $A$ take OR of the premise gates, private to $B$ take AND, and on a shared variable $x_i$ take the selector $x_i ? g_2 : g_1$ (four De Morgan gates). Induction shows that the gate value at $a$ tells on which side the line survives once $x = a$ is fixed; in the monotone case the selector simplifies to a monotone combination.

## Depends on

- [Interpolants of split CNF formulas](interpolants-of-split-cnf-formulas.md)
- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Monotone circuits](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997.
- P. Pudlák, "Lower Bounds for Resolution and Cutting Plane Proofs and Monotone Computations", The Journal of Symbolic Logic 62(3), 981–998, 1997.
