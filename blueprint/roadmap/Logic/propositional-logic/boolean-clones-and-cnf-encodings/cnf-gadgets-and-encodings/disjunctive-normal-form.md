# Disjunctive normal form

A *term* over a set $V$ of variables is a finite conjunction $\ell_1 \wedge \dots \wedge \ell_k$ of literals (variables or negated variables); it is true under an assignment $\sigma : V \to \{0,1\}$ when every literal is true. A formula in *disjunctive normal form* (DNF) is a finite disjunction $T_1 \vee \dots \vee T_m$ of terms; it is true under $\sigma$ when some term is. Negating every literal turns a term into a clause, and the negation of a DNF formula is the CNF formula whose clauses are the negated terms. The *model count* of a DNF formula $\varphi$ is the number of assignments of the variables occurring in $\varphi$ that satisfy it.

## Depends on

- [CNF formula](../../conjunctive-normal-form/cnf.md)

## Sources

- S. Arora and B. Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009.
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
