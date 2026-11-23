# Plugging a term into an STLC context

Let $E$ be a typed one-hole context whose hole
has type $A$ in variable context $\Gamma$ and which produces a term of type $B$ in variable
context $\Delta$. For a term $t$ of type $A$ in $\Gamma$, the plugged term $E[t]$ of type $B$
in $\Delta$ is defined by recursion on $E$: $[\,][t] = t$, $(E\,a)[t] = E[t]\,a$,
$(f\,E)[t] = f\,E[t]$ and $(\lambda.\,E)[t] = \lambda.\,E[t]$, where $[\,]$ is the bare hole,
$E\,a$ applies $E$ to a term $a$, $f\,E$ applies a term $f$ to $E$, and $\lambda.\,E$ puts $E$
under a lambda. No renaming is applied, so a lambda above the hole may bind free variables
of $t$.
