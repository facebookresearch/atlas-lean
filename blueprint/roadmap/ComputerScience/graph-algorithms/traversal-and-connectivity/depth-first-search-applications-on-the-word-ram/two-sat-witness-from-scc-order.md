# Satisfying assignments of 2-CNF formulas from SCC order

Let $\varphi$ be a 2-CNF formula with implication graph $G_\varphi$ (arcs $\neg a \to b$ and $\neg b \to a$ for every clause $a \vee b$), and let the strongly connected components be indexed in a topological order of the condensation, as produced by Kosaraju's algorithm. If no variable $x$ lies in the same component as $\neg x$, and no clause of $\varphi$ is empty (every clause has one or two literals), then the assignment setting $x$ to true exactly when the component of $x$ comes after the component of $\neg x$ satisfies $\varphi$.

## Proof sketch

A one-literal clause $(a)$ is read as $a \vee a$, with the arc $\neg a \to a$. If a clause $a \vee b$ were falsified, then $\neg a$ and $\neg b$ are true, so the components of $\neg a$ are after those of $a$ and similarly for $b$; the arc $\neg a \to b$ forces the index of $b$ to be at least that of $\neg a$, giving a cyclic chain of inequalities that skew symmetry of $G_\varphi$ turns into a contradiction.

## Depends on

- [Implication graph as a finite directed graph](../../../../Logic/propositional-logic/2-satisfiability/implication-graph.md)
- [Kosaraju's algorithm computes the strongly connected components in condensation order](kosaraju-scc-correctness.md)

## Proof depends on

- [Correctness of the SCC-based 2-SAT procedure](../../../../Logic/propositional-logic/2-satisfiability/decide2-sat-eq-true-iff.md)

## Sources

- B. Aspvall, M. F. Plass and R. E. Tarjan, "A Linear-Time Algorithm for Testing the Truth of Certain Quantified Boolean Formulas", Information Processing Letters 8(3), 1979.
