# DPLL search with an explicit trail

The **trail-based DPLL search** on a CNF formula $\varphi$ keeps a stack (the **trail**) of literals assumed true, each marked as a first or a second branch. One step inspects the partial assignment of the trail: if it satisfies every clause, the search stops with it; if it falsifies some clause, the search **backtracks** by popping all second branches from the top and replacing the topmost first branch $\ell$ by the second branch $\neg\ell$, or reports unsatisfiability if no first branch remains; otherwise it applies unit propagation when a clause is unit, and else pushes a first branch on a fresh variable. The binary tree of branchings explored is the **search tree**; its leaves are labelled by the first falsified clause.

## Depends on

- [The DPLL procedure](../../../Logic/propositional-logic/dpll-algorithm/a-deterministic-dpll-solver/dpll.md)
- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- M. Davis, G. Logemann and D. Loveland, "A Machine Program for Theorem-Proving", Communications of the ACM 5(7), 1962.
- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT Modulo Theories: From an Abstract Davis-Putnam-Logemann-Loveland Procedure to DPLL(T)", Journal of the ACM 53(6), 2006.
