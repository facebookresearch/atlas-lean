# Accepted LRAT proofs refute CNF formulas

Let $\varphi$ be a propositional formula in conjunctive normal form. If the LRAT proof checker accepts a proof for $\varphi$, translated clause by clause with the same variables and polarities, then $\varphi$ is not satisfiable. This transfers the soundness of the checker across the translation, which preserves the evaluation of every clause under every assignment.

## Sources

- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient certified RAT verification", *CADE 2017*, LNCS 10395, Springer, 2017, <http://www.cs.cmu.edu/~mheule/publications/lrat.pdf>: Section 4 (the statement that an accepted proof preserves satisfiability).
