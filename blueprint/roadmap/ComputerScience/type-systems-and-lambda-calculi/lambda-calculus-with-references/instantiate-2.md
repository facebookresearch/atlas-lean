# Substitution of a term for variable zero

For terms $t$ and $s$, the instantiation of $t$
by $s$ applies to $t$ the parallel substitution that sends the de Bruijn index $0$ to $s$ and
each index $x + 1$ to the variable $x$. Thus the free occurrences of variable $0$ in $t$ are
replaced by $s$, with the free variables of $s$ raised by the number of binders crossed, and
every other free variable of $t$ is lowered by one.

This is the substitution of β-reduction, written $\uparrow^{-1}([0 \mapsto \uparrow^1 s]\,t)$ in
TAPL Section 6.3; TAPL's $[0 \mapsto s]\,t$ alone does not lower the other free variables.
