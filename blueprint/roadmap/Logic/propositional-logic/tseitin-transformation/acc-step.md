# One step of the linear-time Tseitin builder

Let $c$ map a gate literal and two operand
literals to a list of clauses, and let $(a, \varphi_A, k_A)$ and $(b, \varphi_B, k_B)$ be the
results for the two operands, each a literal, a clause list and a next free gate number. The step
returns the positive literal $g$ of the variable $2k_B + 1$, the clause list $c(g, a, b)$ followed
by $\varphi_B$, and the next free gate number $k_B + 1$. Neither $\varphi_A$ nor $k_A$ is used: in
the builder, $\varphi_B$ is the accumulator, which already holds both operands' clauses.
