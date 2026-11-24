# Tseitin encoding with gates numbered from $k$

Fix a map $\iota$ from atoms to natural
numbers. Given a formula $A$ and a gate number $k$, the encoding returns a literal naming $A$, a
list of defining clauses and the next unused gate number. For an atom $a$ it returns the
positive literal of variable $2\iota(a)$, no clauses, and $k$. For $A \circ B$ with $\circ$ one of
$\wedge$, $\vee$, $\to$, it encodes $A$ from gate $k$, obtaining a literal $a$, clauses $C_A$ and a
gate number $k'$, then $B$ from gate $k'$, obtaining $b$, $C_B$ and $k''$; it returns the positive
literal $g$ of variable $2k''+1$, the clauses $C_A$, then $C_B$, then the three defining clauses
of $g$ for $a \circ b$, and $k''+1$.

Its list concatenations make it quadratic; the Tseitin CNF is computed by a linear-time builder
that produces the same clauses in another order.
