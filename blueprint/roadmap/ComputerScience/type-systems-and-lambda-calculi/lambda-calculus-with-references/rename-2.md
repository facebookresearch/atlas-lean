# Renaming the variables of a term

Given a renaming $\rho : \mathbb{N} \to \mathbb{N}$ of
de Bruijn indices, renaming a term by $\rho$ replaces each variable $x$ by $\rho(x)$; renames
the body of an abstraction $\lambda{:}T.\,t$ by the lift of $\rho$ (which sends $0$ to $0$ and
each $x + 1$ to $\rho(x) + 1$), keeping the type annotation $T$; leaves the unit value and store
locations unchanged; and acts componentwise on applications, allocations, dereferences and
assignments.
