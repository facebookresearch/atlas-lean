# The CPS translation commutes with instantiation by a value or variable

Fix an answer
type $R$ and write $\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types,
contexts (entrywise) and terms. Let $N$ be a term of type $B$ in a context $A, \Gamma$, let $v$
be a term of type $A$ in $\Gamma$, and let $p$ be a term of type $\llbracket A \rrbracket$ in
$\llbracket \Gamma \rrbracket$ related to $v$ by the value translation $\Psi$ (a variable is related
to the corresponding variable, $\lambda x. M$ to $\lambda x. \llbracket M \rrbracket$). Writing
$N[u]$ for $N$ with its newest free variable replaced by $u$, we have
$\llbracket N[v] \rrbracket = \llbracket N \rrbracket[p]$.
