# Elaboration of raw STLC terms

Assume equality of base types is decidable. Elaboration in
a context $\Gamma$ of simple types sends a raw term either to failure or to a checked term in
$\Gamma$ (a simple type together with an intrinsically typed term of that type in $\Gamma$), by
recursion on the raw term. A variable with de Bruijn index $n$ elaborates to the variable at
position $n$ of $\Gamma$ (counting from $0$ at the front), with the type stored there, and fails
if $\Gamma$ has at most $n$ entries. A lambda with parameter type $A$ and body $b$ elaborates $b$
in $\Gamma$ extended by $A$ at the front; if that gives type $B$, it returns the lambda at type
$A \to B$, and otherwise it fails. An application of $f$ to $a$ elaborates $f$ and $a$ in
$\Gamma$, and succeeds, returning the application at type $B$, exactly when $f$ gets a function
type $A \to B$ and $a$ gets type $A$; otherwise it fails.
