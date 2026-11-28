# MAX-E3SAT seven-eighths bound for a CNF formula

For any [CNF formula](../conjunctive-normal-form/cnf.md) `φ` over variables in $\mathbb{N}$ (a list of clauses, each a list of literals $(x, b)$ with $x \in \mathbb{N}$), with [clause satisfaction](../conjunctive-normal-form/satisfies-2.md) under assignments $v : \mathbb{N} \to \{\mathrm{true}, \mathrm{false}\}$: if every clause of `φ` has three literals on three distinct variables, some assignment satisfies the clauses at no fewer than $7/8$ of the positions of `φ`. A clause repeated in `φ` counts once per position.
