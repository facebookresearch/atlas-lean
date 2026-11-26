# Extended resolution

An *extension* introduces a definition $x \leftrightarrow p \vee (c_1 \wedge \dots \wedge c_k)$ with a variable $x$ that occurs neither in $F$, nor in an earlier instruction, nor in the definition's right-hand side, and literals $p, c_1, \dots, c_k$ on pairwise distinct variables, by adding its CNF clauses $x \vee \bar p$, $x \vee \bar c_1 \vee \dots \vee \bar c_k$ and $\bar x \vee p \vee c_j$ for each $j$. An *extended-resolution proof* of a CNF formula $F$ is a clausal proof (as for [DRAT proofs](drat-proofs.md)) each of whose instructions adds a resolvent of two clauses of the accumulated formula or introduces an extension, and whose last accumulated formula contains the empty clause. Tseitin's original rule allowed only definitions $x \leftrightarrow \bar a \vee \bar b$, from which the general ones are derivable.

Extensions preserve satisfiability: as $x$ is new, a model of the accumulated formula extends to one of the added clauses by giving $x$ the value of $p \vee (c_1 \wedge \dots \wedge c_k)$. The freshness of $x$ in its own right-hand side is needed: the definition $x \leftrightarrow \bar x \vee q$ added to the satisfiable formula $\{\bar q\}$ amounts to $x \leftrightarrow \bar x$ and makes it unsatisfiable.

## Depends on

- [DRAT proofs](drat-proofs.md)

## Sources

- B. Kiesl, A. Rebola-Pardo, M. J. H. Heule and A. Biere, "Simulating strong practical proof systems with extended resolution", *Journal of Automated Reasoning* 64:1247–1267, 2020, <https://cca.informatik.uni-freiburg.de/papers/KieslRebolaPardoHeuleBiere-JAR20.pdf>, Section 3 (extension instructions with a variable that does not occur in earlier instructions, and their CNF conversion; that $x$ does not occur in $F$ or in its own definition is written out here) and Section 3.1 (extended resolution and Tseitin's original definitions).
