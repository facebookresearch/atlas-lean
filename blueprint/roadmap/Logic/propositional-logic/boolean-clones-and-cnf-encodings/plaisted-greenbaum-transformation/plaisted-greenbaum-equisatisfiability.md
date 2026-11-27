# Plaisted–Greenbaum: the polarity-aware clause form is equisatisfiable

For every propositional formula $A$, the CNF formula $\mathrm{PG}(A)$ is satisfiable if and only if $A$ is satisfiable. Moreover $\mathrm{PG}(A)$ has at most $3s + 1$ clauses, each with at most three literals, where $s$ is the number of non-atomic subformula occurrences of $A$; in particular its size is linear in the size of $A$. Unlike the Tseitin encoding, $\mathrm{PG}(A)$ is in general not equivalent to $A$ over the extended variables and does not preserve the number of models.

## Proof sketch

Combine the soundness lemma (models of the clause form restrict to models of $A$) with the completeness lemma (the Tseitin extension of a model of $A$ satisfies the clause form). The size bound counts at most three clauses per polarity-instance of a binary connective plus the unit clause.

## Depends on

- [Plaisted–Greenbaum clause form](plaisted-greenbaum-clause-form.md)
- [Satisfiability of a CNF formula](../../conjunctive-normal-form/cnfsat.md)

## Proof depends on

- [Models of the Plaisted–Greenbaum form satisfy the formula](plaisted-greenbaum-soundness.md)
- [Satisfying assignments extend to models of the Plaisted–Greenbaum form](plaisted-greenbaum-completeness.md)

## Sources

- D. A. Plaisted and S. Greenbaum, "A Structure-Preserving Clause Form Translation", Journal of Symbolic Computation 2(3), 293–304, 1986.
