# A DPLL solver that emits LRAT certificates

There is a DPLL solver (splitting and unit propagation, without the pure-literal rule) that on every CNF formula $\varphi$ terminates and returns either a total assignment satisfying $\varphi$ or an LRAT certificate accepted by an LRAT checker for $\varphi$. In particular $\varphi$ is satisfiable if and only if the solver returns an assignment, and unsatisfiable formulas always receive a checkable certificate obtained by compiling the tree-like resolution refutation read off the failing search tree: the DPLL method corresponds to tree-like resolution (Buss and Nordström, Section 7.3.3), and each resolvent becomes an LRAT addition step whose antecedents are its two premises, since an LRAT addition step lists the clauses resolved or propagated, in order, to obtain the new clause (Pollitt, Fleury and Biere, Section 2; Cruz-Filipe et al., Section 3).

## Proof sketch

On an unsatisfiable formula, the failing search tree yields a tree-like resolution refutation; each resolvent is RUP from its two premises, so the refutation becomes LRAT addition steps with at most two hints each (the premises, in the order in which they become unit and then falsified), ending with the empty clause.

## Depends on

- [DPLL search with an explicit trail](dpll-explicit-trail-search.md)
- [Accepted LRAT proofs refute CNF formulas](../../../Logic/propositional-logic/proof-certificates/accepted-lrat-proofs-refute-cnf-formulas.md)

## Proof depends on

- [Failing DPLL search trees give tree-like resolution refutations](../../../Logic/propositional-logic/sat-solving/failing-dpll-search-trees-give-tree-like.md)
- [LRAT addition steps certify RUP and RAT clauses](../../../Logic/propositional-logic/proof-certificates/lrat-addition-steps-certify-rup-and-rat-clauses.md)
- [RUP steps and resolution steps simulate each other](../../../Logic/propositional-logic/proof-certificates/clausal-proof-certificates/lrat-certificates-to-resolution.md)

## Sources

- M. Davis, G. Logemann and D. Loveland, "A Machine Program for Theorem-Proving", Communications of the ACM 5(7), 1962.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction (CADE-26), LNCS 10395, Springer, 2017.
- F. Pollitt, M. Fleury and A. Biere, "Faster LRAT Checking Than Solving with CaDiCaL", 26th International Conference on Theory and Applications of Satisfiability Testing (SAT 2023), LIPIcs 271, Schloss Dagstuhl, 2023, Article 21 (Section 2).
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in A. Biere, M. Heule, H. van Maaren and T. Walsh (eds.), Handbook of Satisfiability, 2nd edition, IOS Press, 2021, Chapter 7 (Section 7.3.3).
