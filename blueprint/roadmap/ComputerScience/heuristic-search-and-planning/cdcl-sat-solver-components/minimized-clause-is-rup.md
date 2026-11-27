# Minimized learned clauses are derivable by unit propagation

Let $D$ be a clause learned by conflict analysis, obtained by resolving reason clauses in reverse assignment order starting from a falsified (conflicting) clause, as for the first-UIP clause, and let $D'$ be obtained from $D$ by recursive minimization. Then $D'$ is a reverse-unit-propagation (RUP) consequence of the clause database: an LRAT addition step for $D'$ is accepted by an LRAT checker when its hints are, in order, the unit clauses of any removed level-$0$ literals, then the reason clauses of the removed literals and of the literals visited recursively while removing them, each placed after the reasons of the literals it depends on, and finally the chain of reason clauses that justifies $D$ in conflict analysis, ending with the conflicting clause. This is how Pollitt, Fleury and Biere justify minimized (and shrunken) learned clauses in LRAT (Section 3.1, Algorithm 1).

## Proof sketch

Assume the negations of the literals of $D'$. Processing the removed and recursively visited literals in this order, when all other literals of the reason $R$ of $\neg y$ are false (they lie in $D'$ or were handled earlier), $R$ is unit and propagates $\neg y$; afterwards every literal of $D$ is false, and the chain that justifies $D$ propagates to the conflict. Minimization removes literals only along resolution paths in the implication graph (Sörensson and Biere), which is why the reasons of the removed literals suffice. Derived, not stated in this form by the sources: when $D$ is already in the database, the hints may end with $D$ itself instead of its justifying chain.

## Depends on

- [Recursive minimization of learned clauses](learned-clause-minimization.md)
- [RUP and RAT clauses](../../../Logic/propositional-logic/proof-certificates/rup-and-rat-clauses.md)
- [LRAT addition steps certify RUP and RAT clauses](../../../Logic/propositional-logic/proof-certificates/lrat-addition-steps-certify-rup-and-rat-clauses.md)

## Sources

- F. Pollitt, M. Fleury and A. Biere, "Faster LRAT Checking Than Solving with CaDiCaL", 26th International Conference on Theory and Applications of Satisfiability Testing (SAT 2023), LIPIcs 271, Schloss Dagstuhl, 2023, Article 21 (Section 3.1, Algorithm 1).
- N. Sörensson and A. Biere, "Minimizing Learned Clauses", Theory and Applications of Satisfiability Testing (SAT 2009), LNCS 5584, Springer, 2009.
- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient Certified RAT Verification", Automated Deduction (CADE-26), LNCS 10395, Springer, 2017.
