# Occurrence splitting preserves satisfiability and not-all-equal satisfiability

For every CNF formula $\varphi$: (1) $\mathrm{Occ}_3(\varphi)$ is satisfiable if and only if $\varphi$ is; (2) $\mathrm{Occ}_3(\varphi)$ is not-all-equal satisfiable (in the NAE sense applied to the original clauses, with the cycle clauses read as equalities) if and only if $\varphi$ is; (3) every variable of $\mathrm{Occ}_3(\varphi)$ occurs at most three times, the clause width does not increase beyond $\max(2, w(\varphi))$, and the construction is computable in polynomial time. Hence SAT restricted to formulas with at most three occurrences per variable is NP-complete.

## Proof sketch

Implication cycles force all copies of a variable to agree, so models correspond bijectively; under NAE semantics a binary cycle clause $\neg a \vee b$ is again an equality constraint. Polynomial time is clear from the explicit indexing.

## Depends on

- [Occurrence splitting of a CNF formula](occurrence-splitting.md)
- [Not-all-equal satisfiability](../../../../TheoryOfComputation/np-completeness/satisfiability/exact-one-and-not-all-equal-satisfiability/not-all-equal-satisfiability.md)

## Proof depends on

- [Binary implication cycles and chains](binary-implication-cycles.md)
- [3SAT is NP-complete](../../../../TheoryOfComputation/np-completeness/satisfiability/3-satisfiability/sat3-dec-np-complete.md)

## Sources

- C. H. Papadimitriou, Computational Complexity, Addison-Wesley, 1994.
- C. A. Tovey, "A Simplified NP-Complete Satisfiability Problem", Discrete Applied Mathematics 8(1), 85–89, 1984.
