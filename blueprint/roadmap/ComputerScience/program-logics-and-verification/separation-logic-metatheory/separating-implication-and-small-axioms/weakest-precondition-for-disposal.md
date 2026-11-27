# Weakest precondition for disposal

For every assertion $R$, the triple $\{(E \mapsto -) \ast R\}\ \mathrm{dispose}(E)\ \{R\}$ is derivable from the [small axiom](small-axioms-of-separation-logic.md) for disposal by the frame rule, which applies to every $R$ because disposal modifies no variable, and the rule of consequence with $\mathrm{emp} \ast R \Leftrightarrow R$. Its precondition is the weakest precondition of $\mathrm{dispose}(E)$ for $R$.

## Depends on

- [Small axioms of separation logic](small-axioms-of-separation-logic.md)

## Sources

- P. O'Hearn, J. Reynolds and H. Yang, "Local reasoning about programs that alter data structures", *Computer Science Logic (CSL 2001)*, LNCS 2142, Springer, 2001, pp. 1–19, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/localreasoning.pdf>, Section 4 (derived laws, the rule for $\mathrm{dispose}(E)$).
