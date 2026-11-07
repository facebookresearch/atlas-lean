# Linear-time Tseitin builder

Fix a map $\iota$ from atoms to natural numbers. Given a
formula $A$, a gate number $k$ and a clause list $\mathit{acc}$, the builder returns a literal
naming $A$, a clause list and the next unused gate number. For an atom $a$ it returns the
positive literal of variable $2\iota(a)$, the list $\mathit{acc}$ unchanged, and $k$. For
$A \circ B$ with $\circ$ one of $\wedge$, $\vee$, $\to$, it runs on $A$ from gate $k$ with
accumulator $\mathit{acc}$, obtaining a literal $a$, a list $L_A$ and a gate number $k'$, then on
$B$ from gate $k'$ with accumulator $L_A$, obtaining $b$, $L_B$ and $k''$; it returns the positive
literal $g$ of variable $2k''+1$, the three defining clauses of $g$ for $a \circ b$ followed by
$L_B$, and $k''+1$.

Unlike the reference Tseitin encoding, which concatenates the operands' clause lists, it
prepends each gate's clauses to the accumulator, so it runs in linear time and the clauses come
out in a different order.
