# The call-by-value CPS translation commutes with renaming

Fix an answer type $R$ and
write $\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types, contexts
(entrywise) and terms. For every renaming $\rho$ from a context $\Gamma$ to a context $\Delta$ and
every term $t$ of type $A$ in $\Gamma$, the translation of the renamed term $t[\rho]$ equals the
renaming of $\llbracket t \rrbracket$ along the translated renaming from
$\llbracket \Gamma \rrbracket$ to $\llbracket \Delta \rrbracket$, which sends the translation of
each variable $x$ of $\Gamma$ to the translation of $\rho(x)$.
