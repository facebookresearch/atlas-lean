# DRAT proofs

A *clausal proof* of a CNF formula $F = C_1 \wedge \dots \wedge C_m$ is a sequence $C_1, \dots, C_m, I_{m+1}, \dots, I_n$ of the clauses of $F$ followed by *instructions*: additions $\langle a, C\rangle$ and deletions $\langle d, C\rangle$ of clauses, and, in extended resolution, extensions. It determines accumulated formulas $F_0, \dots, F_n$: $F_i = \{C_1, \dots, C_i\}$ for $i \le m$, and afterwards $F_i$ is $F_{i-1}$ with the clause of $I_i$ added or deleted, or, for an extension introducing a definition $\varphi$, $F_{i-1} \cup \mathrm{cnf}(\varphi)$, where $\mathrm{cnf}(\varphi)$ is the set of CNF clauses of the definition. A *DRAT proof* is a clausal proof whose additions each add a clause that is a [RUP or a RAT](../proof-certificates/rup-and-rat-clauses.md) in $F_{i-1}$, whose deletions are arbitrary, and whose last accumulated formula contains the empty clause.

A DRAT proof certifies unsatisfiability: additions [preserve satisfiability](adding-a-rat-clause-preserves-satisfiability.md) and deletions cannot turn a satisfiable formula unsatisfiable, so a satisfiable $F$ never reaches the empty clause.

## Depends on

- [RUP and RAT clauses](../proof-certificates/rup-and-rat-clauses.md)
- [Adding a RAT clause preserves satisfiability](adding-a-rat-clause-preserves-satisfiability.md)

## Sources

- B. Kiesl, A. Rebola-Pardo, M. J. H. Heule and A. Biere, "Simulating strong practical proof systems with extended resolution", *Journal of Automated Reasoning* 64:1247–1267, 2020, <https://cca.informatik.uni-freiburg.de/papers/KieslRebolaPardoHeuleBiere-JAR20.pdf>, Section 3: clausal proofs and accumulated formulas, and Section 3.2 (DRAT).
- N. Wetzler, M. J. H. Heule and W. A. Hunt Jr., "DRAT-trim: efficient checking and trimming using expressive clausal proofs", in *Theory and Applications of Satisfiability Testing (SAT 2014)*, LNCS 8561, Springer, 2014, pp. 422–429, <https://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf>, Section 3: the DRAT proof format, the formulas $F^i_P$, and the RUP and RAT checks.
