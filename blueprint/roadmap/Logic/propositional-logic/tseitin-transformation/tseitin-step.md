# One step of the Tseitin encoding

Given a rule $\mathit{cl}$ assigning to literals $g$, $a$,
$b$ a list of defining clauses, and the results $(a, C_A, k_A)$ and $(b, C_B, k_B)$ of encoding
the two operands of a binary connective (each a literal, a clause list and a next unused gate
number), the step returns the positive literal $g$ of variable $2k_B+1$, the clause list $C_A$,
then $C_B$, then $\mathit{cl}(g, a, b)$, and the next gate number $k_B+1$.
