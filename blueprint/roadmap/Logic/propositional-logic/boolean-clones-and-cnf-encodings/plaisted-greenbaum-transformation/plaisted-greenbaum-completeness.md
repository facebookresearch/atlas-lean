# Satisfying assignments extend to models of the Plaisted–Greenbaum form

Let $A$ be a propositional formula and $\tau$ an assignment of its atoms with $A$ true under $\tau$. Extend $\tau$ by setting $p_B$ to the truth value of $B$ under $\tau$ for every subformula $B$ (the Tseitin extension). The extended assignment satisfies every clause of $\mathrm{PG}(A)$, since every definitional clause is one direction of a biconditional that holds under this extension.

## Proof sketch

Each clause of $\mathrm{PG}(A)$ is a clause of the full Tseitin encoding of $A$, which is satisfied by the Tseitin extension; the unit clause holds because $A$ is true.

## Depends on

- [Plaisted–Greenbaum clause form](plaisted-greenbaum-clause-form.md)
- [Tseitin correctness](../../tseitin-transformation/eval-bool-iff-exists-satisfies-tseitin.md)

## Sources

- D. A. Plaisted and S. Greenbaum, "A Structure-Preserving Clause Form Translation", Journal of Symbolic Computation 2(3), 293–304, 1986.
