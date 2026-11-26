# RUP and RAT clauses

Let $F$ be a CNF formula. A clause $C = c_1 \vee \dots \vee c_k$ is a *RUP* (reverse unit propagation clause, also called an asymmetric tautology) in $F$ if unit propagation derives a conflict on $F \wedge \bar c_1 \wedge \dots \wedge \bar c_k$; write $F \vdash_1 C$. A clause $C \vee p$ is a *RAT* (resolution asymmetric tautology) on the literal $p$ in $F$ if, for every clause $D \vee \bar p \in F$, the resolvent $C \vee D$ is a RUP in $F$. Every resolvent of two clauses of $F$ and every clause subsumed by a clause of $F$ is a RUP in $F$, and every nonempty RUP in $F$ is a RAT on each of its literals.

A clause $C$ is *blocked* by a literal $p \in C$ in $F$ if every resolvent of $C$ upon $p$ with a clause of $F$ is a tautology; every blocked clause is a RAT.

## Sources

- B. Kiesl, A. Rebola-Pardo, M. J. H. Heule and A. Biere, "Simulating strong practical proof systems with extended resolution", *Journal of Automated Reasoning* 64:1247–1267, 2020, <https://cca.informatik.uni-freiburg.de/papers/KieslRebolaPardoHeuleBiere-JAR20.pdf>, Section 2: Definition 1 (RUP) and the remarks after it; Section 3.2: Definition 4 (RAT) and Example 1; Section 5: Definition 7 (blocked clauses) and the remark that every blocked clause is a RAT.
- N. Wetzler, M. J. H. Heule and W. A. Hunt Jr., "DRAT-trim: efficient checking and trimming using expressive clausal proofs", in *Theory and Applications of Satisfiability Testing (SAT 2014)*, LNCS 8561, Springer, 2014, pp. 422–429, <https://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf>, Section 2: Definition 1 (asymmetric literal addition), the properties AT (RUP) and RAT.
