# Adding a RAT clause preserves satisfiability

If a clause $C \vee p$ is a [RAT](../proof-certificates/rup-and-rat-clauses.md) on $p$ in a CNF formula $F$, then $F$ and $F \wedge (C \vee p)$ are both satisfiable or both unsatisfiable.

**Proof idea.** A model of $F$ that falsifies $C \vee p$ becomes a model of $F \wedge (C \vee p)$ when $p$ is made true: a clause $D \vee \bar p$ of $F$ that this falsifies would give a resolvent $C \vee D$ false in the original model, although $C \vee D$ is a RUP in $F$ and hence implied by $F$.

## Depends on

- [RUP and RAT clauses](../proof-certificates/rup-and-rat-clauses.md)

## Sources

- B. Kiesl, A. Rebola-Pardo, M. J. H. Heule and A. Biere, "Simulating strong practical proof systems with extended resolution", *Journal of Automated Reasoning* 64:1247–1267, 2020, <https://cca.informatik.uni-freiburg.de/papers/KieslRebolaPardoHeuleBiere-JAR20.pdf>, Section 3.2: the statement after Example 1 (with its proof idea), citing Järvisalo, Heule and Biere (IJCAR 2012).
- N. Wetzler, M. J. H. Heule and W. A. Hunt Jr., "DRAT-trim: efficient checking and trimming using expressive clausal proofs", in *Theory and Applications of Satisfiability Testing (SAT 2014)*, LNCS 8561, Springer, 2014, pp. 422–429, <https://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf>, Section 2: if a clause $C \notin F$ has property RAT with respect to $F$, then $F$ and $F \cup \{C\}$ are satisfiability equivalent.
