# The CPS translation commutes with weakening

Fix an answer type $R$ and write
$\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types, contexts (entrywise)
and terms. For every term $t$ of type $A$ in a context $\Gamma$ and every type $B$, the translation
of the weakening of $t$ to the context $B, \Gamma$ is the weakening of $\llbracket t \rrbracket$ to
the context $\llbracket B \rrbracket, \llbracket \Gamma \rrbracket$.
