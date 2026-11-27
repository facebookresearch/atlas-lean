# Restrictions of resolution refutations

Let $\rho$ be a partial assignment and $\varphi\restriction_\rho$ the formula obtained by deleting the clauses satisfied by $\rho$ and removing the falsified literals from the others. If $\varphi$ has a resolution refutation with $s$ lines and width $w$, then $\varphi\restriction_\rho$ has a resolution refutation with at most $s$ lines and width at most $w$. Moreover, for a variable $x$: if $\varphi\restriction_{x=0}$ has a refutation of width at most $w-1$ and $\varphi\restriction_{x=1}$ has one of width at most $w$, and every clause of $\varphi$ has width at most $w$, then $\varphi$ has a refutation of width at most $w$.

## Proof sketch

Apply $\rho$ to every line: a satisfied line is dropped and its uses are bypassed by the surviving premise, resolution steps on fixed variables collapse to a premise, and restriction never increases width. For the second part, add the literal $x$ back to the first refutation to derive $x$ in width $w$, resolve it with the clauses of $\varphi$, and follow the second refutation.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Restriction of a CNF formula by a literal](../../propositional-logic/conjunctive-normal-form/restrict-2.md)
- [Width of a derivation](../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Sources

- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001: Section 2.2 and Lemmas 3.1–3.2.
- P. Beame and T. Pitassi, "Simplified and Improved Resolution Lower Bounds", Proceedings of the 37th IEEE Symposium on Foundations of Computer Science (FOCS), 1996.
