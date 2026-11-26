# Constraint satisfaction instances and their hypergraphs

A constraint satisfaction (CSP) instance is a triple $I = (V, D, C)$ of a set $V$ of variables, a domain $D$, and a set $C$ of
constraints $\langle (v_1, \dots, v_k), R \rangle$ with $k \ge 1$ and $R$ a $k$-ary relation on $D$, given by listing its tuples. A
solution is a map $\alpha : V \to D$ with $(\alpha(v_1), \dots, \alpha(v_k)) \in R$ for every constraint. The size of a constraint
is $k + k \cdot |R|$, and $\|I\| = |V| + |D| + \sum_{c \in C} \|c\|$. The hypergraph $H_I$ has vertex set $V$ and a hyperedge
$\{v_1, \dots, v_k\}$ for every constraint. For a class $\mathcal H$ of hypergraphs, $\mathrm{Csp}(\mathcal H)$ is the problem
of deciding whether an instance $I$ with $H_I \in \mathcal H$ has a solution. Evaluating a conjunctive query on a database is a
CSP instance with one constraint per atom, and its answers are the projections of the solutions to the free variables.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Sources

- M. Grohe and D. Marx, "Constraint solving via fractional edge covers", *ACM Trans. Algorithms* 11(1) (2014) 4; arXiv:1711.04506 <https://arxiv.org/abs/1711.04506>, Sections 2.1–2.2 and the paragraph before Theorem 4.14.
