# Weakening of typing

If a term $t$ has type $T$ in a variable context $\Gamma$ under a
store typing $S$, then for every type $A$, the term obtained from $t$ by shifting each free de
Bruijn variable up by one has type $T$ under $S$ in the context obtained from $\Gamma$ by adding
$A$ in front as variable $0$.
