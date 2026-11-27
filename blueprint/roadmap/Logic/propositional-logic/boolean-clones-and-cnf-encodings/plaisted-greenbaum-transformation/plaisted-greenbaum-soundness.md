# Models of the Plaisted–Greenbaum form satisfy the formula

Let $A$ be a propositional formula and $\sigma$ an assignment to the atoms of $A$ and the definition variables of $\mathrm{PG}(A)$. If $\sigma$ satisfies $\mathrm{PG}(A)$ then the restriction of $\sigma$ to the atoms satisfies $A$. More precisely, for every subformula occurrence $B$: if the occurrence is positive then $\sigma(p_B) = 1$ implies $B$ is true under $\sigma$, and if it is negative then $B$ true under $\sigma$ implies $\sigma(p_B) = 1$.

## Proof sketch

Induction on the subformula: the one-sided definitional clause of the given polarity propagates the implication from $p_B$ to $p_C \circ p_D$, and the induction hypotheses for $C$ and $D$ (with the polarity of $C$ flipped for $\to$) finish each case; the unit clause $p_A$ then gives the truth of $A$.

## Depends on

- [Plaisted–Greenbaum clause form](plaisted-greenbaum-clause-form.md)

## Sources

- D. A. Plaisted and S. Greenbaum, "A Structure-Preserving Clause Form Translation", Journal of Symbolic Computation 2(3), 293–304, 1986.
