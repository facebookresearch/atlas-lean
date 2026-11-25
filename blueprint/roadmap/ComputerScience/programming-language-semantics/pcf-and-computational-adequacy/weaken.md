# Weakening of PCF terms

Let $\Gamma$ be a context and $A$, $B$ types. Weakening sends a
PCF term $t$ of type $A$ in context $\Gamma$ to the term of type $A$ in the context obtained by
prepending a new variable of type $B$ to $\Gamma$, by renaming every free variable of $t$ to its
successor, that is, by shifting each de Bruijn index up by one.
