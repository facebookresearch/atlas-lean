# CPS translation at a base type with the identity continuation

Fix an interpretation $I$
of the base types, let $t$ be a term of base type $b$ in context $\Gamma$, and take the answer
type to be $b$; write $\overline{\Gamma}$ and $\overline{t}$ for the call-by-value CPS
translations of $\Gamma$ and $t$, and $[t]_\eta$ for the denotation of $t$ in an environment
$\eta$. If $\eta$ and $\eta'$ are related environments for $\Gamma$ and $\overline{\Gamma}$, then
$[\overline{t}]_{\eta'}(\mathrm{id}) = [t]_\eta$, where $\mathrm{id}$ is the identity on $I(b)$.
