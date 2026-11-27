# CNF encoding of a parity constraint

Let $B$ be a finite set of variables and $c \in \{0,1\}$. The constraint $\bigoplus_{x \in B} x = c$ is expressed without auxiliary variables by the CNF formula with one clause $C_y$ for each assignment $y : B \to \{0,1\}$ with $\bigoplus_{x\in B} y(x) \ne c$, where $C_y$ is the clause of the $|B|$ literals falsified by $y$. It has exactly $2^{|B|-1}$ clauses of width $|B|$ (for $B \ne \emptyset$), and no CNF formula on the variables $B$ alone has fewer clauses.

## Proof sketch

Each $C_y$ excludes exactly the point $y$. For minimality, every point of the wrong parity is an isolated false point, so any CNF computing parity has a full-width clause for each of them.

## Depends on

- [CNF formula](../../conjunctive-normal-form/cnf.md)

## Proof depends on

- [DNF and CNF size lower bounds from isolated inputs; parity needs $2^{n-1}$ terms](../../../../TheoryOfComputation/circuit-complexity/circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/normal-form-size-lower-bounds/dnf-cnf-lower-bound-from-isolated-inputs.md)

## Sources

- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
- A. Urquhart, "Hard Examples for Resolution", Journal of the ACM 34(1), 209–219, 1987.
