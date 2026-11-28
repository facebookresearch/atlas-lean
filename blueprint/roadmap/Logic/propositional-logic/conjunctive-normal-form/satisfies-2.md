# Satisfaction of a clause

An assignment $v : \mathbb{N} \to \{\mathrm{true},
\mathrm{false}\}$ satisfies a CNF clause $C$ when at least one literal of $C$ is satisfied by $v$,
that is, $C$ contains a literal $(x, b)$ with $v(x) = b$.

The same notion for a clause given as a finite set of literals rather than a list is satisfaction by some literal $(x, b)$ of the set with $v(x) = b$; enumerating the set as a list gives the same condition, since order and repetition do not affect the existence of such a literal. In either form no assignment satisfies the empty clause.
