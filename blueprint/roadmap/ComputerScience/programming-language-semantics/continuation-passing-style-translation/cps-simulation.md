# Plotkin's simulation theorem, big-step form

Fix an answer type $R$ and write
$\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types, contexts (entrywise)
and terms. If a term $M$ of type $A$ in a context $\Gamma$ evaluates to $V$ under call-by-value
big-step evaluation, then there is a term $p$ related to $V$ by the value translation $\Psi$ (a
variable is related to the corresponding variable, $\lambda x. N$ to
$\lambda x. \llbracket N \rrbracket$) such that for every value $K$ of type
$\llbracket A \rrbracket \to R$ in $\llbracket \Gamma \rrbracket$ and every term $w$, the
application $\llbracket M \rrbracket\, K$ evaluates to $w$ if and only if $K\, p$ evaluates
to $w$.
