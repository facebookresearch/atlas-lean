# A CDCL solver with watched literals returns models or LRAT refutations

Consider a CDCL solver that is an instance of abstract DPLL with learning, uses two watched literals for propagation, first-UIP conflict analysis with recursive clause minimization, VSIDS decisions with phase saving, and Luby restarts, and records each learned clause as an LRAT addition step whose hints are the justification chain of its conflict analysis (the reason clauses resolved, ending with the conflicting clause, preceded for a minimized clause by the reasons of the removed literals), as the CDCL solver of Pollitt, Fleury and Biere does natively (Section 3.1). On every CNF formula $\varphi$ on which it terminates, it returns either a total assignment satisfying $\varphi$, or an LRAT certificate that an LRAT checker accepts for $\varphi$, which is then unsatisfiable. The verdict is that of abstract DPLL with learning (Nieuwenhuis, Oliveras and Tinelli, Theorem 2.12); the certificate is the sequence of learned clauses, each a RUP clause for the current database (Buss and Nordström, Sections 7.3.1.3 and 7.3.2), written with LRAT hints. Termination is a separate property of the strategy: the termination theorem for abstract DPLL with learning gives it when Learn and Forget steps cannot alternate forever and restarts have strictly increasing periodicity; Luby restart intervals are unbounded but not increasing, so that theorem does not apply to them directly.

## Proof sketch

Every move is a move of abstract DPLL with learning, whose invariant gives soundness of models; each first-UIP clause is RUP from the current database with its reasons as hints in trail order followed by the conflict clause, each minimized clause stays RUP, and a conflict at decision level $0$ yields the empty clause, so the log of additions ending in the empty clause is an accepted certificate.

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)
- [Two-watched-literal scheme](two-watched-literal-scheme.md)
- [VSIDS branching heuristic](vsids-branching-heuristic.md)
- [Phase saving](phase-saving.md)
- [The Luby restart sequence](luby-restart-sequence.md)
- [Recursive minimization of learned clauses](learned-clause-minimization.md)
- [Accepted LRAT proofs refute CNF formulas](../../../Logic/propositional-logic/proof-certificates/accepted-lrat-proofs-refute-cnf-formulas.md)
- [RUP and RAT clauses](../../../Logic/propositional-logic/proof-certificates/rup-and-rat-clauses.md)

## Proof depends on

- [Completeness of propagation with two watched literals](watched-literal-invariant.md)
- [Minimized learned clauses are derivable by unit propagation](minimized-clause-is-rup.md)
- [Final states of abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/final-states-of-abstract-dpll-with-learning.md)
- [Termination of abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/termination-of-abstract-dpll-with-learning.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT Modulo Theories: From an Abstract Davis-Putnam-Logemann-Loveland Procedure to DPLL(T)", Journal of the ACM 53(6), 2006.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction (CADE-26), LNCS 10395, Springer, 2017.
- F. Pollitt, M. Fleury and A. Biere, "Faster LRAT Checking Than Solving with CaDiCaL", 26th International Conference on Theory and Applications of Satisfiability Testing (SAT 2023), LIPIcs 271, Schloss Dagstuhl, 2023, Article 21 (Section 3.1).
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in A. Biere, M. Heule, H. van Maaren and T. Walsh (eds.), Handbook of Satisfiability, 2nd edition, IOS Press, 2021, Chapter 7 (Sections 7.3.1.3 and 7.3.2).
