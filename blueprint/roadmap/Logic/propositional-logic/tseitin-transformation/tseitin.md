# Tseitin CNF

For a map $\iota$ from atoms to natural numbers and a formula $A$, run the
linear-time Tseitin builder on $A$ with gates numbered from $0$ and the empty accumulator,
obtaining a literal $\ell$ naming $A$ and a clause list $C$. The Tseitin CNF of $A$ is the unit
clause $[\ell]$ followed by $C$.
