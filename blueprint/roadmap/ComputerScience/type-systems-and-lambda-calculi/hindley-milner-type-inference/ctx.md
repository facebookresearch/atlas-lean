# Typing context

A typing context over base types $B$ is a finite list of bindings
$(x, \sigma)$, each pairing a name $x$ (a string) with a type scheme $\sigma$ over $B$. A name
may be bound more than once; the first binding of a name in the list is the visible one.
