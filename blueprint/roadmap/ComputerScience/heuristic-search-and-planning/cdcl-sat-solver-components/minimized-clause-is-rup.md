# Minimized learned clauses are derivable by unit propagation

If $D'$ is obtained from a learned clause $D$ by removing redundant literals, then $D'$ is a reverse-unit-propagation (RUP) consequence of the clause database together with $D$: assuming the negations of the literals of $D'$, unit propagation along the reason clauses of the removed literals derives the negation of every removed literal and then falsifies $D$. Consequently an LRAT step for $D'$ whose hints list those reasons (and the unit clauses of any removed level-$0$ literals) in trail order, followed by $D$, is accepted by an LRAT checker.

## Proof sketch

Process the removed and recursively visited literals in trail order: when all other literals of the reason $R$ of $\neg y$ are false (they lie in $D'$ or were handled earlier), $R$ is unit and propagates $\neg y$. Afterwards every literal of $D$ is false.

## Depends on

- [Recursive minimization of learned clauses](learned-clause-minimization.md)
- [RUP and RAT clauses](../../../Logic/propositional-logic/proof-certificates/rup-and-rat-clauses.md)

## Proof depends on

- [LRAT addition steps certify RUP and RAT clauses](../../../Logic/propositional-logic/proof-certificates/lrat-addition-steps-certify-rup-and-rat-clauses.md)

## Sources

- N. Sörensson and A. Biere, "Minimizing Learned Clauses", Theory and Applications of Satisfiability Testing (SAT 2009), LNCS 5584, Springer, 2009.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction (CADE-26), LNCS 10395, Springer, 2017.
