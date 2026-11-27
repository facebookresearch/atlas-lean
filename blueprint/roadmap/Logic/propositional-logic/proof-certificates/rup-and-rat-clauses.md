# RUP and RAT clauses

A CNF formula $F$ is a finite set of clauses, a clause a finite set of literals. A *unit clause* has one literal. *Unit clause
propagation* on a formula repeatedly takes a unit clause $(l)$ and removes every occurrence of $\bar l$ from the other clauses; it stops
when nothing changes or when some clause becomes empty, a *conflict*. For a clause $C$, $\bar C$ is the conjunction of the negations of
its literals.

- $C$ is an *asymmetric tautology* (AT) with respect to $F$, also called a *reverse unit propagation* (RUP) clause, if unit clause
  propagation on $F \wedge \bar C$ reaches a conflict.
- For clauses $C \ni l$ and $D \ni \bar l$, the *resolvent* on $l$ is $C \otimes_l D = (C \setminus \{l\}) \cup (D \setminus \{\bar l\})$.
- $C$ is a *resolution asymmetric tautology* (RAT) on $l \in C$ with respect to $F$ if for every $D \in F$ with $\bar l \in D$ the resolvent
  $C \otimes_l D$ is AT with respect to $F$. The LRAT checker tests the equivalent condition that $C \cup (D \setminus \{\bar l\})$ is AT with
  respect to $F$.
- Formulas are *logically equivalent* if they have the same models, and *satisfiability-equivalent* if both are satisfiable or
  both are unsatisfiable.

## Depends on

- [Satisfiability of a CNF formula](../conjunctive-normal-form/cnfsat.md)

## Sources

- L. Cruz-Filipe, M. J. H. Heule, W. A. Hunt Jr., M. Kaufmann and P. Schneider-Kamp, "Efficient certified RAT verification", *CADE 2017*, LNCS 10395, Springer, 2017, <http://www.cs.cmu.edu/~mheule/publications/lrat.pdf>: Section 2 (unit clause propagation, AT and RAT).
- M. Järvisalo, M. J. H. Heule and A. Biere, "Inprocessing rules", *IJCAR 2012*, LNCS 7364, Springer, 2012, <http://fmv.jku.at/papers/JarvisaloHeuleBiere-IJCAR12.pdf>: Section 2 (resolvents, logical and satisfiability equivalence) and Definition 3 (the resolution variant RP of a property P, giving RAT).
