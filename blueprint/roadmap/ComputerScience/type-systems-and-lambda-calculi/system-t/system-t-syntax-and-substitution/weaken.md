# Weakening of System T terms

Weakening sends a term of type $A$ in context $\Gamma$ to the
term of type $A$ in the context obtained by prepending a variable of type $B$ to $\Gamma$. Each
variable occurrence that refers to $\Gamma$ has its de Bruijn index shifted up by one; an
occurrence bound inside the term keeps its index, since renaming lifts the shift under each
$\lambda$-binder and the lift fixes the newest variable.
