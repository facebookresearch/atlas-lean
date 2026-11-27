# Satisfaction of a clause

An assignment $v : \mathbb{N} \to \{\mathrm{true},
\mathrm{false}\}$ satisfies a CNF clause $C$ when at least one literal of $C$ is satisfied by $v$,
that is, $C$ contains a literal $(x, b)$ with $v(x) = b$.

Equivalently, the Boolean value of $C$ under $v$, true exactly when some literal $(x, b)$ of $C$ has $v(x) = b$ and false otherwise (in particular false for the empty clause), is true exactly when $v$ satisfies $C$.
