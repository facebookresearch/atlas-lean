# Inequality translation of CNF formulas for semialgebraic proofs

A CNF formula is translated into polynomial constraints by sending a clause $C$ to the inequality $\sum_{v \in C} x_v + \sum_{\neg v \in C}(1 - x_v) - 1 \ge 0$, adding the box constraints $x_v \ge 0$ and $1 - x_v \ge 0$ for every variable, and the Boolean axioms $x_v^2 - x_v = 0$ as equations. The formula is satisfiable iff these constraints have a real common solution, and every Boolean model gives one. A degree-one pseudo-expectation is the same as a fractional point of the LP relaxation.

## Depends on

- [Positivstellensatz (sum-of-squares) refutations](positivstellensatz-refutations.md)
- [The cutting planes proof system](../cutting-planes/cutting-planes-proof-system.md)
- [Degree-$d$ pseudo-expectations](pseudo-expectations.md)

## Sources

- D. Grigoriev, E. A. Hirsch and D. V. Pasechnik, "Complexity of Semialgebraic Proofs", Moscow Mathematical Journal 2(4), 647–679, 2002.
