# Variable lookup

Given a context $\Gamma$, a list of types, and a natural number $n$,
looking up the de Bruijn index $n$ in $\Gamma$ either fails or returns a type $A$ together with
an intrinsic variable of type $A$ in $\Gamma$. It is defined by recursion: lookup fails in the
empty context; index $0$ in the context $A :: \Gamma$, obtained by adding $A$ at the front of
$\Gamma$, returns $A$ with the zero variable; and index $n + 1$ in $B :: \Gamma$ looks up $n$ in
$\Gamma$, fails if that fails, and otherwise returns the same type with the successor of the
variable found.
