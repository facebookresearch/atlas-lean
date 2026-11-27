# Constraint satisfaction instances and their hypergraphs

A constraint satisfaction (CSP) instance is a triple $I = (V, D, C)$ of a finite set $V$ of variables, a finite domain $D$, and
a finite set $C$ of constraints $\langle (v_1, \dots, v_k), R \rangle$ with $k \ge 1$ and $R$ a $k$-ary relation on $D$, given by
listing its tuples, such that every variable occurs in the scope of some constraint. A
solution is a map $\alpha : V \to D$ with $(\alpha(v_1), \dots, \alpha(v_k)) \in R$ for every constraint. The size of a constraint
is $k + k \cdot |R|$, and $\|I\| = |V| + |D| + \sum_{c \in C} \|c\|$. The hypergraph $H_I$ has vertex set $V$ and a hyperedge
$\{v_1, \dots, v_k\}$ for every constraint. For a class $\mathcal H$ of hypergraphs, $\mathrm{Csp}(\mathcal H)$ is the problem
of deciding whether an instance $I$ with $H_I \in \mathcal H$ has a solution. Evaluating a conjunctive query on a database
becomes a CSP instance as follows: atoms with constants only are checked separately (the query is false if one is not a
fact); in every other atom, positions holding a constant or repeating a variable are used to select the matching facts and
then projected away, leaving one constraint on the distinct variables of the atom. The answers are the projections of the
solutions to the free variables; for $\mathrm{Answer}() \mathrel{:-} R(a)$ there is no constraint at all.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Sources

- M. Grohe and D. Marx, "Constraint solving via fractional edge covers", *ACM Trans. Algorithms* 11(1) (2014) 4; arXiv:1711.04506 <https://arxiv.org/abs/1711.04506>, Sections 2.1–2.2 and the paragraph before Theorem 4.14.
