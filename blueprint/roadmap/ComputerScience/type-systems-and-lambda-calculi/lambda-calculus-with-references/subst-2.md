# Parallel substitution in a term

Given a substitution $\sigma$ assigning a term to each
de Bruijn index, substituting $\sigma$ into a term replaces each variable $x$ by $\sigma(x)$;
substitutes into the body of an abstraction $\lambda{:}T.\,t$ the lift of $\sigma$ (which sends
$0$ to the variable $0$ and each $x + 1$ to $\sigma(x)$ with every free variable raised by one),
keeping the type annotation $T$; leaves the unit value and store locations unchanged; and acts
componentwise on applications, allocations, dereferences and assignments.
