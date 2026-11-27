# A DPLL solver that emits LRAT certificates

There is a DPLL solver (splitting and unit propagation, without the pure-literal rule) that on every CNF formula $\varphi$ terminates and returns either a total assignment satisfying $\varphi$ or an LRAT certificate accepted by an LRAT checker for $\varphi$. In particular $\varphi$ is satisfiable if and only if the solver returns an assignment, and unsatisfiable formulas always receive a checkable certificate obtained by compiling the tree-like resolution refutation read off the failing search tree.

## Proof sketch

On an unsatisfiable formula, the failing search tree yields a tree-like resolution refutation; each resolvent is RUP from its two premises, so the refutation becomes LRAT addition steps with at most two hints each (the premises, in the order in which they become unit and then falsified), ending with the empty clause.

## Depends on

- [DPLL search with an explicit trail](dpll-explicit-trail-search.md)
- [Accepted LRAT proofs refute CNF formulas](../../../Logic/propositional-logic/proof-certificates/accepted-lrat-proofs-refute-cnf-formulas.md)

## Proof depends on

- [Failing DPLL search trees give tree-like resolution refutations](../../../Logic/propositional-logic/sat-solving/failing-dpll-search-trees-give-tree-like.md)
- [LRAT addition steps certify RUP and RAT clauses](../../../Logic/propositional-logic/proof-certificates/lrat-addition-steps-certify-rup-and-rat-clauses.md)

## Sources

- M. Davis, G. Logemann and D. Loveland, "A Machine Program for Theorem-Proving", Communications of the ACM 5(7), 1962.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction (CADE-26), LNCS 10395, Springer, 2017.
