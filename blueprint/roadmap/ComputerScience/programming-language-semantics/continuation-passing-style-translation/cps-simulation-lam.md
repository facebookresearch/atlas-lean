# Simulation for terms evaluating to an abstraction

Fix an answer type $R$ and write
$\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types, contexts (entrywise)
and terms. If a term $M$ of type $A \to B$ in a context $\Gamma$ evaluates to $\lambda x. N$ under
call-by-value big-step evaluation, then for every value $K$ of type
$\llbracket A \to B \rrbracket \to R$ in $\llbracket \Gamma \rrbracket$ and every term $w$ of type
$R$, the application $\llbracket M \rrbracket\, K$ evaluates to $w$ if and only if
$K\, (\lambda x. \llbracket N \rrbracket)$ evaluates to $w$.
