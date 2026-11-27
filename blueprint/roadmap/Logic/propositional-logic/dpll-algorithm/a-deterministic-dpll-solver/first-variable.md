# First variable of a CNF formula

For a CNF formula $\varphi$, read as a list of clauses,
this returns the variable of the first literal of the first nonempty clause of $\varphi$, that
is, the first variable occurring in $\varphi$ in source order, and returns nothing when every
clause of $\varphi$ is empty (in particular when $\varphi$ has no clauses).
