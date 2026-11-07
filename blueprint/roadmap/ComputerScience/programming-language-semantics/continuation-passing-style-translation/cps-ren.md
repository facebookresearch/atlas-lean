# Translated renaming

Fix an answer type $R$ and write $\llbracket \Gamma \rrbracket$ for the
context obtained by applying the call-by-value CPS type translation to every entry of $\Gamma$. A
renaming $\rho$ from $\Gamma$ to $\Delta$ induces the renaming from $\llbracket \Gamma \rrbracket$
to $\llbracket \Delta \rrbracket$ that sends the translation of each variable $x$ of $\Gamma$ (the
variable at the same position) to the translation of $\rho(x)$.
