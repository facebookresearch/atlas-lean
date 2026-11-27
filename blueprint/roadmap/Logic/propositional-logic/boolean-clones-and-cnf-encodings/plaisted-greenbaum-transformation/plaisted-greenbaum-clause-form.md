# Plaisted–Greenbaum clause form

Let $A$ be a propositional formula. Introduce a fresh variable $p_B$ for every non-atomic subformula $B = C \circ D$ of $A$ (with $\circ \in \{\wedge,\vee,\to\}$), and let $p_x = x$ for an atom $x$; equal subformulas share their variable. For every occurrence of $B$ with positive polarity, add the clauses of the one-sided definition $p_B \to (p_C \circ p_D)$; for every occurrence with negative polarity add the clauses of $(p_C \circ p_D) \to p_B$; a subformula occurring with both polarities receives both. The *Plaisted–Greenbaum clause form* $\mathrm{PG}(A)$ is the conjunction of these definitional clauses together with the unit clause $p_A$. Compared with the Tseitin transformation it keeps only one implication direction of each definition, so it has at most as many clauses and every clause has at most three literals.

## Depends on

- [Polarity of a subformula occurrence](subformula-polarity.md)
- [Tseitin CNF](../../tseitin-transformation/tseitin.md)
- [CNF formula](../../conjunctive-normal-form/cnf.md)

## Sources

- D. A. Plaisted and S. Greenbaum, "A Structure-Preserving Clause Form Translation", Journal of Symbolic Computation 2(3), 293–304, 1986.
